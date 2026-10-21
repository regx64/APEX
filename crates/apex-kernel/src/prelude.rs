//! Bootstrap declarations written directly against the kernel.

use crate::builder::*;
use crate::env::{Env, KResult};
use crate::inductive::InductiveDecl;
use crate::level::Level;
use crate::term::Mult;

/// `Eq`, `Nat`, `Nat.add`, `Nat.mul`, `Bool`, `Unit` and `List`.
pub fn add_prelude(env: &mut Env) -> KResult<()> {
    let u = Level::param("u");

    // inductive Eq.{u} {α : Sort u} (a : α) : α → Prop | refl : Eq a a
    env.add_inductive(InductiveDecl {
        name: "Eq".into(),
        lparams: vec!["u".into()],
        nparams: 2,
        ty: pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_("a", v("α"), arrow(v("α"), prop())),
        )
        .build()?,
        ctors: vec![(
            "Eq.refl".into(),
            pi_m(
                Mult::Zero,
                "α",
                sort_(u.clone()),
                pi_(
                    "a",
                    v("α"),
                    app_(cl("Eq", vec![u.clone()]), vec![v("α"), v("a"), v("a")]),
                ),
            )
            .build()?,
        )],
    })?;

    // inductive Nat : Type | zero | succ (n : Nat)
    env.add_inductive(InductiveDecl {
        name: "Nat".into(),
        lparams: vec![],
        nparams: 0,
        ty: type_().build()?,
        ctors: vec![
            ("Nat.zero".into(), c("Nat").build()?),
            ("Nat.succ".into(), arrow(c("Nat"), c("Nat")).build()?),
        ],
    })?;

    // def Nat.add (n m : Nat) : Nat := Nat.rec (fun _ => Nat) n (fun _ ih => succ ih) m
    let nat = || c("Nat");
    env.add_def(
        "Nat.add",
        &[],
        arrow(nat(), arrow(nat(), nat())).build()?,
        lam_(
            "n",
            nat(),
            lam_(
                "m",
                nat(),
                app_(
                    cl("Nat.rec", vec![Level::of_nat(1)]),
                    vec![
                        lam_("_", nat(), nat()),
                        v("n"),
                        lam_(
                            "k",
                            nat(),
                            lam_("ih", nat(), app_(c("Nat.succ"), vec![v("ih")])),
                        ),
                        v("m"),
                    ],
                ),
            ),
        )
        .build()?,
    )?;

    // def Nat.mul (n m : Nat) : Nat := Nat.rec (fun _ => Nat) 0 (fun _ ih => ih + n) m
    env.add_def(
        "Nat.mul",
        &[],
        arrow(nat(), arrow(nat(), nat())).build()?,
        lam_(
            "n",
            nat(),
            lam_(
                "m",
                nat(),
                app_(
                    cl("Nat.rec", vec![Level::of_nat(1)]),
                    vec![
                        lam_("_", nat(), nat()),
                        c("Nat.zero"),
                        lam_(
                            "k",
                            nat(),
                            lam_("ih", nat(), app_(c("Nat.add"), vec![v("ih"), v("n")])),
                        ),
                        v("m"),
                    ],
                ),
            ),
        )
        .build()?,
    )?;

    // inductive Bool : Type | false | true      (constructor order matters for Bool.rec)
    env.add_inductive(InductiveDecl {
        name: "Bool".into(),
        lparams: vec![],
        nparams: 0,
        ty: type_().build()?,
        ctors: vec![
            ("Bool.false".into(), c("Bool").build()?),
            ("Bool.true".into(), c("Bool").build()?),
        ],
    })?;

    // inductive Unit : Type | unit
    env.add_inductive(InductiveDecl {
        name: "Unit".into(),
        lparams: vec![],
        nparams: 0,
        ty: type_().build()?,
        ctors: vec![("Unit.unit".into(), c("Unit").build()?)],
    })?;

    // inductive List.{u} (α : Type u) : Type u | nil | cons (head : α) (tail : List α)
    let tu = || sort_(u.clone().succ());
    let list_a = || app_(cl("List", vec![u.clone()]), vec![v("α")]);
    env.add_inductive(InductiveDecl {
        name: "List".into(),
        lparams: vec!["u".into()],
        nparams: 1,
        ty: pi_m(Mult::Zero, "α", tu(), tu()).build()?,
        ctors: vec![
            (
                "List.nil".into(),
                pi_m(Mult::Zero, "α", tu(), list_a()).build()?,
            ),
            (
                "List.cons".into(),
                pi_m(
                    Mult::Zero,
                    "α",
                    tu(),
                    arrow(v("α"), arrow(list_a(), list_a())),
                )
                .build()?,
            ),
        ],
    })?;
    crate::below::add_pprod(env)?;
    add_io(env)?;
    add_logic(env)?;
    add_quot(env)?;
    for ind in ["Nat", "Bool", "Unit", "List"] {
        env.add_below_brec(ind)?;
    }
    Ok(())
}

/// `String`, `IO` and their primitive operations. These are axioms for the
/// kernel (they never compute there); the interpreter gives them meaning.
fn add_io(env: &mut Env) -> KResult<()> {
    let io = |a: Raw| app_(c("IO"), vec![a]);
    env.add_axiom("String", &[], type_().build()?)?;
    env.add_axiom(
        "String.append",
        &[],
        arrow(c("String"), arrow(c("String"), c("String"))).build()?,
    )?;
    env.add_axiom("Nat.toString", &[], arrow(c("Nat"), c("String")).build()?)?;
    env.add_axiom("IO", &[], arrow(type_(), type_()).build()?)?;
    env.add_axiom(
        "IO.pure",
        &[],
        pi_m(Mult::Zero, "α", type_(), arrow(v("α"), io(v("α")))).build()?,
    )?;
    env.add_axiom(
        "IO.bind",
        &[],
        pi_m(
            Mult::Zero,
            "α",
            type_(),
            pi_m(
                Mult::Zero,
                "β",
                type_(),
                arrow(io(v("α")), arrow(arrow(v("α"), io(v("β"))), io(v("β")))),
            ),
        )
        .build()?,
    )?;
    env.add_axiom("IO.print", &[], arrow(c("String"), io(c("Unit"))).build()?)?;
    Ok(())
}

/// Propositional logic and the standard `Eq` lemmas. These are what the tactic
/// framework builds proofs from; each is an ordinary kernel definition.
fn add_logic(env: &mut Env) -> KResult<()> {
    let u = Level::param("u");
    let v_ = Level::param("v");
    let z = Level::zero;
    let eq = |l: &Level, t: Raw, a: Raw, b: Raw| app_(cl("Eq", vec![l.clone()]), vec![t, a, b]);

    // Eq.subst {α a b} (motive : α → Prop) (h : a = b) (m : motive a) : motive b
    env.add_def(
        "Eq.subst",
        &["u"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_(
                "a",
                v("α"),
                pi_(
                    "b",
                    v("α"),
                    pi_(
                        "motive",
                        arrow(v("α"), prop()),
                        pi_(
                            "h",
                            eq(&u, v("α"), v("a"), v("b")),
                            arrow(
                                app_(v("motive"), vec![v("a")]),
                                app_(v("motive"), vec![v("b")]),
                            ),
                        ),
                    ),
                ),
            ),
        )
        .build()?,
        lam_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            lam_(
                "a",
                v("α"),
                lam_(
                    "b",
                    v("α"),
                    lam_(
                        "motive",
                        arrow(v("α"), prop()),
                        lam_(
                            "h",
                            eq(&u, v("α"), v("a"), v("b")),
                            lam_(
                                "m",
                                app_(v("motive"), vec![v("a")]),
                                app_(
                                    cl("Eq.rec", vec![z(), u.clone()]),
                                    vec![
                                        v("α"),
                                        v("a"),
                                        lam_(
                                            "x",
                                            v("α"),
                                            lam_(
                                                "_",
                                                eq(&u, v("α"), v("a"), v("x")),
                                                app_(v("motive"), vec![v("x")]),
                                            ),
                                        ),
                                        v("m"),
                                        v("b"),
                                        v("h"),
                                    ],
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
        .build()?,
    )?;

    // Eq.symm {α a b} (h : a = b) : b = a
    env.add_def(
        "Eq.symm",
        &["u"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_(
                "a",
                v("α"),
                pi_(
                    "b",
                    v("α"),
                    arrow(
                        eq(&u, v("α"), v("a"), v("b")),
                        eq(&u, v("α"), v("b"), v("a")),
                    ),
                ),
            ),
        )
        .build()?,
        lam_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            lam_(
                "a",
                v("α"),
                lam_(
                    "b",
                    v("α"),
                    lam_(
                        "h",
                        eq(&u, v("α"), v("a"), v("b")),
                        app_(
                            cl("Eq.subst", vec![u.clone()]),
                            vec![
                                v("α"),
                                v("a"),
                                v("b"),
                                lam_("x", v("α"), eq(&u, v("α"), v("x"), v("a"))),
                                v("h"),
                                app_(cl("Eq.refl", vec![u.clone()]), vec![v("α"), v("a")]),
                            ],
                        ),
                    ),
                ),
            ),
        )
        .build()?,
    )?;

    // Eq.trans {α a b c} (h₁ : a = b) (h₂ : b = c) : a = c
    env.add_def(
        "Eq.trans",
        &["u"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_(
                "a",
                v("α"),
                pi_(
                    "b",
                    v("α"),
                    pi_(
                        "c",
                        v("α"),
                        arrow(
                            eq(&u, v("α"), v("a"), v("b")),
                            arrow(
                                eq(&u, v("α"), v("b"), v("c")),
                                eq(&u, v("α"), v("a"), v("c")),
                            ),
                        ),
                    ),
                ),
            ),
        )
        .build()?,
        lam_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            lam_(
                "a",
                v("α"),
                lam_(
                    "b",
                    v("α"),
                    lam_(
                        "c",
                        v("α"),
                        lam_(
                            "h1",
                            eq(&u, v("α"), v("a"), v("b")),
                            lam_(
                                "h2",
                                eq(&u, v("α"), v("b"), v("c")),
                                app_(
                                    cl("Eq.subst", vec![u.clone()]),
                                    vec![
                                        v("α"),
                                        v("b"),
                                        v("c"),
                                        lam_("x", v("α"), eq(&u, v("α"), v("a"), v("x"))),
                                        v("h2"),
                                        v("h1"),
                                    ],
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
        .build()?,
    )?;

    // congr_arg {α β a b} (f : α → β) (h : a = b) : f a = f b
    env.add_def(
        "congr_arg",
        &["u", "v"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_m(
                Mult::Zero,
                "β",
                sort_(v_.clone()),
                pi_(
                    "a",
                    v("α"),
                    pi_(
                        "b",
                        v("α"),
                        pi_(
                            "f",
                            arrow(v("α"), v("β")),
                            arrow(
                                eq(&u, v("α"), v("a"), v("b")),
                                eq(
                                    &v_,
                                    v("β"),
                                    app_(v("f"), vec![v("a")]),
                                    app_(v("f"), vec![v("b")]),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
        .build()?,
        lam_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            lam_m(
                Mult::Zero,
                "β",
                sort_(v_.clone()),
                lam_(
                    "a",
                    v("α"),
                    lam_(
                        "b",
                        v("α"),
                        lam_(
                            "f",
                            arrow(v("α"), v("β")),
                            lam_(
                                "h",
                                eq(&u, v("α"), v("a"), v("b")),
                                app_(
                                    cl("Eq.subst", vec![u.clone()]),
                                    vec![
                                        v("α"),
                                        v("a"),
                                        v("b"),
                                        lam_(
                                            "x",
                                            v("α"),
                                            eq(
                                                &v_,
                                                v("β"),
                                                app_(v("f"), vec![v("a")]),
                                                app_(v("f"), vec![v("x")]),
                                            ),
                                        ),
                                        v("h"),
                                        app_(
                                            cl("Eq.refl", vec![v_.clone()]),
                                            vec![v("β"), app_(v("f"), vec![v("a")])],
                                        ),
                                    ],
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
        .build()?,
    )?;

    // inductive True : Prop | intro
    env.add_inductive(InductiveDecl {
        name: "True".into(),
        lparams: vec![],
        nparams: 0,
        ty: prop().build()?,
        ctors: vec![("True.intro".into(), c("True").build()?)],
    })?;
    // inductive False : Prop
    env.add_inductive(InductiveDecl {
        name: "False".into(),
        lparams: vec![],
        nparams: 0,
        ty: prop().build()?,
        ctors: vec![],
    })?;
    // False.elim {C : Sort u} (h : False) : C
    env.add_def(
        "False.elim",
        &["u"],
        pi_m(Mult::Zero, "C", sort_(u.clone()), arrow(c("False"), v("C"))).build()?,
        lam_m(
            Mult::Zero,
            "C",
            sort_(u.clone()),
            lam_(
                "h",
                c("False"),
                app_(
                    cl("False.rec", vec![u.clone()]),
                    vec![lam_("_", c("False"), v("C")), v("h")],
                ),
            ),
        )
        .build()?,
    )?;
    // def Not (p : Prop) : Prop := p → False
    env.add_def(
        "Not",
        &[],
        pi_m(Mult::Zero, "p", prop(), prop()).build()?,
        lam_m(Mult::Zero, "p", prop(), arrow(v("p"), c("False"))).build()?,
    )?;
    // inductive And (a b : Prop) : Prop | intro (left : a) (right : b)
    env.add_inductive(InductiveDecl {
        name: "And".into(),
        lparams: vec![],
        nparams: 2,
        ty: pi_m(
            Mult::Zero,
            "a",
            prop(),
            pi_m(Mult::Zero, "b", prop(), prop()),
        )
        .build()?,
        ctors: vec![(
            "And.intro".into(),
            pi_m(
                Mult::Zero,
                "a",
                prop(),
                pi_m(
                    Mult::Zero,
                    "b",
                    prop(),
                    arrow(v("a"), arrow(v("b"), app_(c("And"), vec![v("a"), v("b")]))),
                ),
            )
            .build()?,
        )],
    })?;
    // inductive Or (a b : Prop) : Prop | inl (h : a) | inr (h : b)
    let or_ctor = |side: bool| {
        pi_m(
            Mult::Zero,
            "a",
            prop(),
            pi_m(
                Mult::Zero,
                "b",
                prop(),
                arrow(
                    if side { v("a") } else { v("b") },
                    app_(c("Or"), vec![v("a"), v("b")]),
                ),
            ),
        )
        .build()
    };
    env.add_inductive(InductiveDecl {
        name: "Or".into(),
        lparams: vec![],
        nparams: 2,
        ty: pi_m(
            Mult::Zero,
            "a",
            prop(),
            pi_m(Mult::Zero, "b", prop(), prop()),
        )
        .build()?,
        ctors: vec![
            ("Or.inl".into(), or_ctor(true)?),
            ("Or.inr".into(), or_ctor(false)?),
        ],
    })?;
    // inductive Exists.{u} {α : Sort u} (p : α → Prop) : Prop | intro (w : α) (h : p w)
    env.add_inductive(InductiveDecl {
        name: "Exists".into(),
        lparams: vec!["u".into()],
        nparams: 2,
        ty: pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_m(Mult::Zero, "p", arrow(v("α"), prop()), prop()),
        )
        .build()?,
        ctors: vec![(
            "Exists.intro".into(),
            pi_m(
                Mult::Zero,
                "α",
                sort_(u.clone()),
                pi_m(
                    Mult::Zero,
                    "p",
                    arrow(v("α"), prop()),
                    pi_(
                        "w",
                        v("α"),
                        arrow(
                            app_(v("p"), vec![v("w")]),
                            app_(cl("Exists", vec![u.clone()]), vec![v("α"), v("p")]),
                        ),
                    ),
                ),
            )
            .build()?,
        )],
    })?;
    // And.left / And.right
    for (name, left) in [("And.left", true), ("And.right", false)] {
        let ab = || app_(c("And"), vec![v("a"), v("b")]);
        let want = || if left { v("a") } else { v("b") };
        env.add_def(
            name,
            &[],
            pi_m(
                Mult::Zero,
                "a",
                prop(),
                pi_m(Mult::Zero, "b", prop(), arrow(ab(), want())),
            )
            .build()?,
            lam_m(
                Mult::Zero,
                "a",
                prop(),
                lam_m(
                    Mult::Zero,
                    "b",
                    prop(),
                    lam_(
                        "h",
                        ab(),
                        app_(
                            cl("And.rec", vec![z()]),
                            vec![
                                v("a"),
                                v("b"),
                                lam_("_", ab(), want()),
                                lam_(
                                    "l",
                                    v("a"),
                                    lam_("r", v("b"), if left { v("l") } else { v("r") }),
                                ),
                                v("h"),
                            ],
                        ),
                    ),
                ),
            )
            .build()?,
        )?;
    }
    Ok(())
}

/// Quotient types and the classical axioms, as in Lean: `Quot.lift` computes on
/// `Quot.mk` (a kernel rule in `whnf`), everything else is an axiom. `funext` is
/// *derived* from `Quot.sound`, not assumed.
fn add_quot(env: &mut Env) -> KResult<()> {
    let u = Level::param("u");
    let v_ = Level::param("v");
    let rel = |al: Raw| arrow(al.clone(), arrow(al, prop()));
    let quot = |u: &Level, al: Raw, r: Raw| app_(cl("Quot", vec![u.clone()]), vec![al, r]);
    // Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u
    env.add_axiom(
        "Quot",
        &["u"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_m(Mult::Zero, "r", rel(v("α")), sort_(u.clone())),
        )
        .build()?,
    )?;
    // Quot.mk {α} (r) (a : α) : Quot r
    env.add_axiom(
        "Quot.mk",
        &["u"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_m(
                Mult::Zero,
                "r",
                rel(v("α")),
                pi_("a", v("α"), quot(&u, v("α"), v("r"))),
            ),
        )
        .build()?,
    )?;
    // Quot.lift {α r} {β : Sort v} (f : α → β) (h : ∀ a b, r a b → f a = f b) : Quot r → β
    let eq_v = |b: Raw, x: Raw, y: Raw| app_(cl("Eq", vec![v_.clone()]), vec![b, x, y]);
    env.add_axiom(
        "Quot.lift",
        &["u", "v"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_m(
                Mult::Zero,
                "r",
                rel(v("α")),
                pi_m(
                    Mult::Zero,
                    "β",
                    sort_(v_.clone()),
                    pi_(
                        "f",
                        arrow(v("α"), v("β")),
                        arrow(
                            pi_(
                                "a",
                                v("α"),
                                pi_(
                                    "b",
                                    v("α"),
                                    arrow(
                                        app_(v("r"), vec![v("a"), v("b")]),
                                        eq_v(
                                            v("β"),
                                            app_(v("f"), vec![v("a")]),
                                            app_(v("f"), vec![v("b")]),
                                        ),
                                    ),
                                ),
                            ),
                            arrow(quot(&u, v("α"), v("r")), v("β")),
                        ),
                    ),
                ),
            ),
        )
        .build()?,
    )?;
    // Quot.ind {α r} {β : Quot r → Prop} (mk : ∀ a, β (Quot.mk r a)) : ∀ q, β q
    env.add_axiom(
        "Quot.ind",
        &["u"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_m(
                Mult::Zero,
                "r",
                rel(v("α")),
                pi_m(
                    Mult::Zero,
                    "β",
                    arrow(quot(&u, v("α"), v("r")), prop()),
                    arrow(
                        pi_(
                            "a",
                            v("α"),
                            app_(
                                v("β"),
                                vec![app_(
                                    cl("Quot.mk", vec![u.clone()]),
                                    vec![v("α"), v("r"), v("a")],
                                )],
                            ),
                        ),
                        pi_("q", quot(&u, v("α"), v("r")), app_(v("β"), vec![v("q")])),
                    ),
                ),
            ),
        )
        .build()?,
    )?;
    // Quot.sound {α r} {a b} : r a b → Quot.mk r a = Quot.mk r b
    let mk = |a: Raw| app_(cl("Quot.mk", vec![u.clone()]), vec![v("α"), v("r"), a]);
    env.add_axiom(
        "Quot.sound",
        &["u"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_m(
                Mult::Zero,
                "r",
                rel(v("α")),
                pi_(
                    "a",
                    v("α"),
                    pi_(
                        "b",
                        v("α"),
                        arrow(
                            app_(v("r"), vec![v("a"), v("b")]),
                            app_(
                                cl("Eq", vec![u.clone()]),
                                vec![quot(&u, v("α"), v("r")), mk(v("a")), mk(v("b"))],
                            ),
                        ),
                    ),
                ),
            ),
        )
        .build()?,
    )?;
    // propext {a b : Prop} : (a → b) → (b → a) → a = b
    env.add_axiom(
        "propext",
        &[],
        pi_(
            "a",
            prop(),
            pi_(
                "b",
                prop(),
                arrow(
                    arrow(v("a"), v("b")),
                    arrow(
                        arrow(v("b"), v("a")),
                        app_(cl("Eq", vec![Level::of_nat(1)]), vec![prop(), v("a"), v("b")]),
                    ),
                ),
            ),
        )
        .build()?,
    )?;
    // inductive Nonempty.{u} (α : Sort u) : Prop | intro (val : α)
    env.add_inductive(InductiveDecl {
        name: "Nonempty".into(),
        lparams: vec!["u".into()],
        nparams: 1,
        ty: pi_m(Mult::Zero, "α", sort_(u.clone()), prop()).build()?,
        ctors: vec![(
            "Nonempty.intro".into(),
            pi_m(
                Mult::Zero,
                "α",
                sort_(u.clone()),
                arrow(
                    v("α"),
                    app_(cl("Nonempty", vec![u.clone()]), vec![v("α")]),
                ),
            )
            .build()?,
        )],
    })?;
    // Classical.choice {α : Sort u} : Nonempty α → α
    env.add_axiom(
        "Classical.choice",
        &["u"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            arrow(app_(cl("Nonempty", vec![u.clone()]), vec![v("α")]), v("α")),
        )
        .build()?,
    )?;
    // funext, derived from Quot.sound:
    //   funext {α} {β : α → Sort v} {f g : Π x, β x} (h : Π x, f x = g x) : f = g
    let fty = || pi_("x", v("α"), app_(v("β"), vec![v("x")]));
    let pi_level = Level::imax(u.clone(), v_.clone());
    let rel_fn = lam_(
        "f",
        fty(),
        lam_(
            "g",
            fty(),
            pi_(
                "x",
                v("α"),
                eq_v(
                    app_(v("β"), vec![v("x")]),
                    app_(v("f"), vec![v("x")]),
                    app_(v("g"), vec![v("x")]),
                ),
            ),
        ),
    );
    let quot_fn = || {
        app_(
            cl("Quot", vec![pi_level.clone()]),
            vec![fty(), rel_fn.clone()],
        )
    };
    // extfunApp : Quot r → Π x, β x
    let ext = lam_(
        "q",
        quot_fn(),
        lam_(
            "x",
            v("α"),
            app_(
                cl("Quot.lift", vec![pi_level.clone(), v_.clone()]),
                vec![
                    fty(),
                    rel_fn.clone(),
                    app_(v("β"), vec![v("x")]),
                    lam_("f", fty(), app_(v("f"), vec![v("x")])),
                    lam_(
                        "f",
                        fty(),
                        lam_(
                            "g",
                            fty(),
                            lam_(
                                "h",
                                app_(rel_fn.clone(), vec![v("f"), v("g")]),
                                app_(v("h"), vec![v("x")]),
                            ),
                        ),
                    ),
                    v("q"),
                ],
            ),
        ),
    );
    let mk_fn = |f: Raw| {
        app_(
            cl("Quot.mk", vec![pi_level.clone()]),
            vec![fty(), rel_fn.clone(), f],
        )
    };
    env.add_def(
        "funext",
        &["u", "v"],
        pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_m(
                Mult::Zero,
                "β",
                arrow(v("α"), sort_(v_.clone())),
                pi_(
                    "f",
                    fty(),
                    pi_(
                        "g",
                        fty(),
                        arrow(
                            pi_(
                                "x",
                                v("α"),
                                eq_v(
                                    app_(v("β"), vec![v("x")]),
                                    app_(v("f"), vec![v("x")]),
                                    app_(v("g"), vec![v("x")]),
                                ),
                            ),
                            app_(
                                cl("Eq", vec![pi_level.clone()]),
                                vec![fty(), v("f"), v("g")],
                            ),
                        ),
                    ),
                ),
            ),
        )
        .build()?,
        lam_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            lam_m(
                Mult::Zero,
                "β",
                arrow(v("α"), sort_(v_.clone())),
                lam_(
                    "f",
                    fty(),
                    lam_(
                        "g",
                        fty(),
                        lam_(
                            "h",
                            pi_(
                                "x",
                                v("α"),
                                eq_v(
                                    app_(v("β"), vec![v("x")]),
                                    app_(v("f"), vec![v("x")]),
                                    app_(v("g"), vec![v("x")]),
                                ),
                            ),
                            app_(
                                cl("congr_arg", vec![pi_level.clone(), pi_level.clone()]),
                                vec![
                                    quot_fn(),
                                    fty(),
                                    mk_fn(v("f")),
                                    mk_fn(v("g")),
                                    ext,
                                    app_(
                                        cl("Quot.sound", vec![pi_level.clone()]),
                                        vec![fty(), rel_fn.clone(), v("f"), v("g"), v("h")],
                                    ),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        )
        .build()?,
    )?;
    Ok(())
}
