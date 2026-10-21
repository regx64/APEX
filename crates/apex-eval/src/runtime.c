/* APEX native runtime: a lazy environment machine over the erased IR (a C port of
   apex-eval's interpreter). The program is the data above; memory is never freed. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

typedef unsigned __int128 u128;
typedef struct V V;
typedef struct Env Env;
struct Env { V *v; Env *next; };

enum { T_NAT, T_STR, T_IO, T_CTOR, T_CLOS, T_FUN, T_ERASED, T_THUNK };
enum { TH_PENDING, TH_DONE, TH_RUNNING };
enum { IO_PURE, IO_BIND, IO_PRINT };
struct V {
  int tag;
  u128 nat;
  const char *s; size_t slen;
  int io; V *a, *b;          /* IO action: pure a / bind a b / print a */
  int gid;                   /* ctor / fun */
  int n; V **args;           /* ctor fields / fun partial args */
  int ir; Env *env;          /* closure body, pending thunk */
  int state; V *result;      /* thunk */
};

static void die(const char *m) { fflush(stdout); fprintf(stderr, "error: %s\n", m); exit(1); }
static V *mk(int tag) { V *v = calloc(1, sizeof(V)); if (!v) die("out of memory"); v->tag = tag; return v; }
static V *ERASED_V;
static V *mk_nat(u128 n) { V *v = mk(T_NAT); v->nat = n; return v; }

static V *force(V *v);
static V *eval(int ir, Env *env);
static V *apply(V *f, V *a);

static V *global(int gid);
static Env *cons(V *v, Env *e) { Env *n = malloc(sizeof(Env)); n->v = v; n->next = e; return n; }
static V *lookup(Env *e, int i) { while (i-- > 0) { if (!e) die("unbound variable"); e = e->next; } if (!e) die("unbound variable"); return e->v; }

static V *delay(int ir, Env *env) {
  const IrNode *n = &IR[ir];
  switch (n->kind) {
  case K_ERASED: return ERASED_V;
  case K_NAT: return mk_nat(((u128)n->hi << 64) | n->lo);
  case K_STR: { V *v = mk(T_STR); v->s = n->s; v->slen = n->len; return v; }
  case K_VAR: return lookup(env, (int)n->lo);
  case K_LAM: { V *v = mk(T_CLOS); v->ir = n->a; v->env = env; return v; }
  default: { V *v = mk(T_THUNK); v->state = TH_PENDING; v->ir = ir; v->env = env; return v; }
  }
}

static V *force(V *v) {
  if (v->tag != T_THUNK) return v;
  if (v->state == TH_DONE) return v->result;
  if (v->state == TH_RUNNING) die("infinite loop: a value depends on itself");
  v->state = TH_RUNNING;
  V *r = eval(v->ir, v->env);
  v->state = TH_DONE; v->result = r;
  return r;
}

static V *eval(int ir, Env *env) {
  const IrNode *n = &IR[ir];
  switch (n->kind) {
  case K_VAR: return force(lookup(env, (int)n->lo));
  case K_LAM: { V *v = mk(T_CLOS); v->ir = n->a; v->env = env; return v; }
  case K_APP: { V *f = eval(n->a, env); V *a = delay(n->b, env); return apply(f, a); }
  case K_GLOBAL: return global(n->a);
  case K_ERASED: return ERASED_V;
  case K_NAT: return mk_nat(((u128)n->hi << 64) | n->lo);
  case K_STR: { V *v = mk(T_STR); v->s = n->s; v->slen = n->len; return v; }
  case K_LET: { V *vv = delay(n->a, env); return eval(n->b, cons(vv, env)); }
  }
  die("bad IR node"); return NULL;
}

static V *exec(int gid, V **args, int nargs);

static V *apply(V *f, V *a) {
  f = force(f);
  if (f->tag == T_CLOS) return eval(f->ir, cons(a, f->env));
  if (f->tag == T_FUN) {
    int n = f->n + 1;
    V **args = malloc(sizeof(V *) * n);
    memcpy(args, f->args, sizeof(V *) * f->n);
    args[f->n] = a;
    if (n == GLOBS[f->gid].arity) return exec(f->gid, args, n);
    V *r = mk(T_FUN); r->gid = f->gid; r->n = n; r->args = args; return r;
  }
  if (f->tag == T_ERASED) return ERASED_V;
  die("applying a value that is not a function"); return NULL;
}

static u128 force_nat(V *v) { v = force(v); if (v->tag != T_NAT) die("expected a natural number"); return v->nat; }
static V *force_str(V *v) { v = force(v); if (v->tag != T_STR) die("expected a string"); return v; }

static int find_ctor(const char *name) {
  for (int i = 0; i < NGLOBS; i++) if (GLOBS[i].kind == G_CTOR && !strcmp(GLOBS[i].name, name)) return i;
  return -1;
}
static V *ctor0(const char *name) {
  int g = find_ctor(name);
  if (g < 0) die("missing constructor");
  return global(g);
}

static V *mk_io(int kind, V *a, V *b) { V *v = mk(T_IO); v->io = kind; v->a = a; v->b = b; return v; }

static V *exec_rec(int gid, V **args, int nargs);

static V *exec(int gid, V **args, int nargs) {
  const Glob *g = &GLOBS[gid];
  (void)nargs;
  switch (g->kind) {
  case G_CTOR: { V *v = mk(T_CTOR); v->gid = gid; v->n = g->arity; v->args = args; return v; }
  case G_REC: return exec_rec(gid, args, nargs);
  case G_PRIM: break;
  default: die("not callable");
  }
  switch (g->prim) {
  case P_NAT_SUCC: { u128 a = force_nat(args[0]), r; if (__builtin_add_overflow(a, (u128)1, &r)) die("Nat overflow"); return mk_nat(r); }
  case P_NAT_ADD: { u128 a = force_nat(args[0]), b = force_nat(args[1]), r; if (__builtin_add_overflow(a, b, &r)) die("Nat overflow"); return mk_nat(r); }
  case P_NAT_MUL: { u128 a = force_nat(args[0]), b = force_nat(args[1]), r; if (__builtin_mul_overflow(a, b, &r)) die("Nat overflow"); return mk_nat(r); }
  case P_STR_APPEND: {
    V *a = force_str(args[0]), *b = force_str(args[1]);
    char *s = malloc(a->slen + b->slen + 1);
    memcpy(s, a->s, a->slen); memcpy(s + a->slen, b->s, b->slen); s[a->slen + b->slen] = 0;
    V *v = mk(T_STR); v->s = s; v->slen = a->slen + b->slen; return v;
  }
  case P_STR_LENGTH: {
    V *a = force_str(args[0]); u128 n = 0;
    for (size_t i = 0; i < a->slen; i++) if (((unsigned char)a->s[i] & 0xC0) != 0x80) n++;
    return mk_nat(n);
  }
  case P_STR_BEQ: {
    V *a = force_str(args[0]), *b = force_str(args[1]);
    return ctor0(a->slen == b->slen && !memcmp(a->s, b->s, a->slen) ? "Bool.true" : "Bool.false");
  }
  case P_NAT_SUB: { u128 a = force_nat(args[0]), b = force_nat(args[1]); return mk_nat(a > b ? a - b : 0); }
  case P_NAT_DIV: { u128 a = force_nat(args[0]), b = force_nat(args[1]); return mk_nat(b ? a / b : 0); }
  case P_NAT_REM: { u128 a = force_nat(args[0]), b = force_nat(args[1]); return mk_nat(b ? a % b : a); }
  case P_NAT_BEQ: { u128 a = force_nat(args[0]), b = force_nat(args[1]); return ctor0(a == b ? "Bool.true" : "Bool.false"); }
  case P_NAT_LT: { u128 a = force_nat(args[0]), b = force_nat(args[1]); return ctor0(a < b ? "Bool.true" : "Bool.false"); }
  case P_WF_FIX: {
    V *ih = mk(T_FUN); ih->gid = WF_IH_GID; ih->n = 5; ih->args = malloc(sizeof(V *) * 5); memcpy(ih->args, args, sizeof(V *) * 5);
    V *step = apply(args[4], args[5]);
    return apply(step, ih);
  }
  case P_WF_IH: return exec(WF_FIX_GID, args, 6);
  case P_QUOT_MK: return force(args[2]);
  case P_QUOT_LIFT: { V *f = force(args[3]); return apply(f, args[5]); }
  case P_NAT_TO_STRING: {
    u128 n = force_nat(args[0]); char buf[64]; int i = 63; buf[i] = 0;
    if (n == 0) buf[--i] = '0';
    while (n) { buf[--i] = '0' + (int)(n % 10); n /= 10; }
    char *s = strdup(buf + i); V *v = mk(T_STR); v->s = s; v->slen = strlen(s); return v;
  }
  case P_IO_PURE: return mk_io(IO_PURE, args[1], NULL);
  case P_IO_BIND: return mk_io(IO_BIND, args[2], args[3]);
  case P_IO_PRINT: return mk_io(IO_PRINT, args[0], NULL);
  }
  die("unknown primitive"); return NULL;
}

static V *rule_cache[NRULES + 1];

static V *exec_rec(int gid, V **args, int nargs) {
  const Glob *g = &GLOBS[gid];
  (void)nargs;
  int midx = g->nparams + g->nmotives + g->nminors + g->nindices;
  V *major = force(args[midx]);
  const Rule *rule = NULL; int rule_idx = -1;
  V **fields = NULL; int nfields = 0;
  if (major->tag == T_NAT) {
    const char *c = major->nat == 0 ? "Nat.zero" : "Nat.succ";
    for (int i = 0; i < g->nrules; i++) if (!strcmp(RULES[g->rules_off + i].ctor, c)) { rule = &RULES[g->rules_off + i]; rule_idx = g->rules_off + i; }
    if (major->nat) { fields = malloc(sizeof(V *)); fields[0] = mk_nat(major->nat - 1); nfields = 1; }
  } else if (major->tag == T_CTOR) {
    const char *c = GLOBS[major->gid].name;
    for (int i = 0; i < g->nrules; i++) if (!strcmp(RULES[g->rules_off + i].ctor, c)) { rule = &RULES[g->rules_off + i]; rule_idx = g->rules_off + i; }
    int np = GLOBS[major->gid].nparams;
    fields = major->args + np; nfields = major->n - np;
  } else if (major->tag == T_ERASED && g->nrules == 1) {
    rule = &RULES[g->rules_off]; rule_idx = g->rules_off;
    nfields = rule->nfields; fields = malloc(sizeof(V *) * (nfields + 1));
    for (int i = 0; i < nfields; i++) fields[i] = ERASED_V;
  } else die("cannot eliminate this value with a recursor");
  if (!rule) die("no recursor rule for this constructor");
  V *rv = rule_cache[rule_idx];
  if (!rv) { rv = eval(rule->rhs, NULL); rule_cache[rule_idx] = rv; }
  V *cur = rv;
  for (int i = 0; i < g->nparams + g->nmotives + g->nminors; i++) cur = apply(cur, args[i]);
  for (int i = 0; i < nfields; i++) cur = apply(cur, fields[i]);
  for (int i = midx + 1; i < g->arity; i++) cur = apply(cur, args[i]);
  return force(cur);
}

static V *globals_cache[NGLOBS + 1];

static V *global(int gid) {
  if (globals_cache[gid]) return globals_cache[gid];
  const Glob *g = &GLOBS[gid];
  V *v;
  switch (g->kind) {
  case G_DEF: v = eval(g->ir, NULL); break;
  case G_ERASED: v = ERASED_V; break;
  case G_NATLIT: v = mk_nat(0); break;
  case G_CTOR:
    if (g->arity == 0) { v = mk(T_CTOR); v->gid = gid; v->n = 0; v->args = NULL; break; }
    /* fallthrough */
  default: v = mk(T_FUN); v->gid = gid; v->n = 0; v->args = NULL; break;
  }
  globals_cache[gid] = v;
  return v;
}

static void print_nat(u128 n) {
  char buf[64]; int i = 63; buf[i] = 0;
  if (n == 0) buf[--i] = '0';
  while (n) { buf[--i] = '0' + (int)(n % 10); n /= 10; }
  fputs(buf + i, stdout);
}

static void show(V *v) {
  v = force(v);
  switch (v->tag) {
  case T_NAT: print_nat(v->nat); break;
  case T_ERASED: fputs("_", stdout); break;
  case T_STR: putchar('"'); fwrite(v->s, 1, v->slen, stdout); putchar('"'); break;
  case T_IO: fputs("<io action>", stdout); break;
  case T_CLOS: case T_FUN: fputs("<function>", stdout); break;
  case T_CTOR: {
    const char *name = GLOBS[v->gid].name;
    if (!strcmp(name, "Unit.unit")) { fputs("()", stdout); break; }
    if (!strcmp(name, "Bool.true")) { fputs("true", stdout); break; }
    if (!strcmp(name, "Bool.false")) { fputs("false", stdout); break; }
    const char *last = strrchr(name, '.'); const char *shortn = last ? last + 1 : name;
    char tyname[256]; tyname[0] = 0;
    if (!strcmp(shortn, "mk") && last) {
      size_t len = (size_t)(last - name); const char *b = name;
      for (size_t i = 0; i < len; i++) if (name[i] == '.') b = name + i + 1;
      size_t l = (size_t)(last - b); if (l > 255) l = 255; memcpy(tyname, b, l); tyname[l] = 0; shortn = tyname;
    }
    int np = GLOBS[v->gid].nparams, first = 1, any = 0;
    for (int i = np; i < v->n; i++) {
      if (force(v->args[i])->tag == T_ERASED) continue;
      if (first) { fputs(shortn, stdout); putchar('('); } else fputs(", ", stdout);
      first = 0; any = 1;
      show(v->args[i]);
    }
    if (any) putchar(')'); else fputs(shortn, stdout);
    break;
  }
  }
}

static void run_io(V *action) {
  int cap = 64, top = 0; V **conts = malloc(sizeof(V *) * cap);
  V *cur = force(action);
  for (;;) {
    if (cur->tag != T_IO) die("expected an IO action");
    V *result;
    if (cur->io == IO_BIND) {
      if (top == cap) { cap *= 2; conts = realloc(conts, sizeof(V *) * cap); }
      conts[top++] = cur->b; cur = force(cur->a); continue;
    } else if (cur->io == IO_PURE) result = cur->a;
    else { V *s = force_str(cur->a); fwrite(s->s, 1, s->slen, stdout); result = ctor0("Unit.unit"); }
    if (top == 0) return;
    V *next = apply(conts[--top], result);
    cur = force(next);
  }
}

static void *run(void *arg) {
  (void)arg;
  ERASED_V = mk(T_ERASED);
  V *m = global(MAIN_GID);
  if (MAIN_IS_IO) run_io(m); else { show(m); putchar('\n'); }
  fflush(stdout);
  return NULL;
}

int main(void) {
  pthread_attr_t attr; pthread_t t;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, (size_t)1 << 30);
  if (pthread_create(&t, &attr, run, NULL)) die("cannot start the main thread");
  pthread_join(t, NULL);
  return 0;
}
