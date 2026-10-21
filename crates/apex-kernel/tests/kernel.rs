use apex_kernel::builder::*;
use apex_kernel::prelude::add_prelude;
use apex_kernel::{Env, InductiveDecl, Level, Mult};

fn env() -> Env {
    let mut e = Env::new();
    add_prelude(&mut e).unwrap();
    e
}

fn nat() -> Raw {
    c("Nat")
}
fn zero() -> Raw {
    c("Nat.zero")
}
fn succ(n: Raw) -> Raw {
    app_(c("Nat.succ"), vec![n])
}
fn add(a: Raw, b: Raw) -> Raw {
    app_(c("Nat.add"), vec![a, b])
}
/// `Eq.{1} Nat a b`
fn eq_nat(a: Raw, b: Raw) -> Raw {
    app_(cl("Eq", vec![Level::of_nat(1)]), vec![nat(), a, b])
}
fn refl_nat(a: Raw) -> Raw {
    app_(cl("Eq.refl", vec![Level::of_nat(1)]), vec![nat(), a])
}

/// congrArg.{u,v} {α : Sort u} {β : Sort v} (f : α → β) (a b : α) (h : a = b) : f a = f b
fn add_congr_arg(e: &mut Env) {
    let (u, vv) = (Level::param("u"), Level::param("v"));
    let eq = |l: &Level, t: Raw, a: Raw, b: Raw| app_(cl("Eq", vec![l.clone()]), vec![t, a, b]);
    let ty = pi_(
        "α",
        sort_(u.clone()),
        pi_(
            "β",
            sort_(vv.clone()),
            pi_(
                "f",
                arrow(v("α"), v("β")),
                pi_(
                    "a",
                    v("α"),
                    pi_(
                        "b",
                        v("α"),
                        pi_(
                            "h",
                            eq(&u, v("α"), v("a"), v("b")),
                            eq(
                                &vv,
                                v("β"),
                                app_(v("f"), vec![v("a")]),
                                app_(v("f"), vec![v("b")]),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    // Eq.rec.{0,u} α a (fun b' _ => f a = f b') (refl (f a)) b h
    let motive = lam_(
        "b'",
        v("α"),
        lam_(
            "_",
            eq(&u, v("α"), v("a"), v("b'")),
            eq(
                &vv,
                v("β"),
                app_(v("f"), vec![v("a")]),
                app_(v("f"), vec![v("b'")]),
            ),
        ),
    );
    let val = lam_(
        "α",
        sort_(u.clone()),
        lam_(
            "β",
            sort_(vv.clone()),
            lam_(
                "f",
                arrow(v("α"), v("β")),
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
                                cl("Eq.rec", vec![Level::zero(), u.clone()]),
                                vec![
                                    v("α"),
                                    v("a"),
                                    motive,
                                    app_(
                                        cl("Eq.refl", vec![vv.clone()]),
                                        vec![v("β"), app_(v("f"), vec![v("a")])],
                                    ),
                                    v("b"),
                                    v("h"),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    e.add_def(
        "congrArg",
        &["u", "v"],
        ty.build().unwrap(),
        val.build().unwrap(),
    )
    .unwrap();
}

#[test]
fn prelude_checks() {
    let e = env();
    assert!(e.get("Nat.rec").is_some());
    assert!(e.get("Eq.rec").is_some());
    assert!(e.get("List.rec").is_some());
}

#[test]
fn recursor_types_have_expected_shape() {
    let e = env();
    let show = |n: &str| e.get(n).unwrap().ty().to_string();
    // Nat.rec.{u} : (motive : Nat → Sort u) → motive zero → ((n : Nat) → motive n → motive (succ n)) → (t : Nat) → motive t
    let nat_rec = show("Nat.rec");
    assert!(nat_rec.contains("Sort u"), "{nat_rec}");
    // Eq lives in Prop but is a subsingleton, so Eq.rec has an extra universe parameter
    let eq_rec_levels = e.get("Eq.rec").unwrap().lparams().len();
    assert_eq!(eq_rec_levels, 2);
}

#[test]
fn nat_add_zero_by_rfl() {
    let mut e = env();
    let ty = pi_("n", nat(), eq_nat(add(v("n"), zero()), v("n")));
    let val = lam_("n", nat(), refl_nat(v("n")));
    e.add_def(
        "Nat.add_zero",
        &[],
        ty.build().unwrap(),
        val.build().unwrap(),
    )
    .unwrap();
}

#[test]
fn zero_add_by_rfl_is_rejected() {
    let mut e = env();
    // 0 + n = n is NOT definitional (recursion is on the second argument)
    let ty = pi_("n", nat(), eq_nat(add(zero(), v("n")), v("n")));
    let val = lam_("n", nat(), refl_nat(v("n")));
    let err = e
        .add_def(
            "Nat.zero_add",
            &[],
            ty.build().unwrap(),
            val.build().unwrap(),
        )
        .unwrap_err();
    assert!(err.0.contains("mismatch"), "{err}");
}

#[test]
fn nat_zero_add_by_induction() {
    let mut e = env();
    add_congr_arg(&mut e);
    let motive = lam_("n", nat(), eq_nat(add(zero(), v("n")), v("n")));
    let step = lam_(
        "k",
        nat(),
        lam_(
            "ih",
            eq_nat(add(zero(), v("k")), v("k")),
            app_(
                cl("congrArg", vec![Level::of_nat(1), Level::of_nat(1)]),
                vec![
                    nat(),
                    nat(),
                    c("Nat.succ"),
                    add(zero(), v("k")),
                    v("k"),
                    v("ih"),
                ],
            ),
        ),
    );
    let val = lam_(
        "n",
        nat(),
        app_(
            cl("Nat.rec", vec![Level::zero()]),
            vec![motive, refl_nat(zero()), step, v("n")],
        ),
    );
    let ty = pi_("n", nat(), eq_nat(add(zero(), v("n")), v("n")));
    e.add_def(
        "Nat.zero_add",
        &[],
        ty.build().unwrap(),
        val.build().unwrap(),
    )
    .unwrap();
}

#[test]
fn ill_typed_application_is_rejected() {
    let mut e = env();
    let err = e
        .add_def(
            "bad",
            &[],
            nat().build().unwrap(),
            app_(c("Nat.succ"), vec![type_()]).build().unwrap(),
        )
        .unwrap_err();
    assert!(err.0.contains("mismatch"), "{err}");
}

#[test]
fn positivity_violation_is_rejected() {
    let mut e = env();
    let err = e
        .add_inductive(InductiveDecl {
            name: "Bad".into(),
            lparams: vec![],
            nparams: 0,
            ty: type_().build().unwrap(),
            ctors: vec![(
                "Bad.mk".into(),
                arrow(arrow(c("Bad"), nat()), c("Bad")).build().unwrap(),
            )],
        })
        .unwrap_err();
    assert!(err.0.contains("positiv"), "{err}");
    assert!(
        e.get("Bad").is_none(),
        "failed declaration must be rolled back"
    );
}

#[test]
fn universe_too_large_is_rejected() {
    let mut e = env();
    let err = e
        .add_inductive(InductiveDecl {
            name: "U".into(),
            lparams: vec![],
            nparams: 0,
            ty: type_().build().unwrap(),
            ctors: vec![("U.mk".into(), arrow(type_(), c("U")).build().unwrap())],
        })
        .unwrap_err();
    assert!(err.0.contains("universe"), "{err}");
}

#[test]
fn undeclared_universe_param_is_rejected() {
    let mut e = Env::new();
    let err = e
        .add_axiom("A", &[], sort_(Level::param("u")).build().unwrap())
        .unwrap_err();
    assert!(err.0.contains("universe"), "{err}");
}

#[test]
fn list_recursion_reduces() {
    let mut e = env();
    // length : List.{0} Nat → Nat
    let u0 = vec![Level::zero()];
    let list_nat = app_(cl("List", u0.clone()), vec![nat()]);
    let motive = lam_("_", list_nat.clone(), nat());
    let cons_case = lam_(
        "h",
        nat(),
        lam_("t", list_nat.clone(), lam_("ih", nat(), succ(v("ih")))),
    );
    let len = lam_(
        "l",
        list_nat.clone(),
        app_(
            cl("List.rec", vec![Level::of_nat(1), Level::zero()]),
            vec![nat(), motive, zero(), cons_case, v("l")],
        ),
    );
    e.add_def(
        "length",
        &[],
        arrow(list_nat.clone(), nat()).build().unwrap(),
        len.build().unwrap(),
    )
    .unwrap();
    // length [0, 0] = 2 by rfl
    let nil = app_(cl("List.nil", u0.clone()), vec![nat()]);
    let cons = |x: Raw, xs: Raw| app_(cl("List.cons", u0.clone()), vec![nat(), x, xs]);
    let two = cons(zero(), cons(zero(), nil));
    let ty = eq_nat(app_(c("length"), vec![two]), succ(succ(zero())));
    e.add_def(
        "length_two",
        &[],
        ty.build().unwrap(),
        refl_nat(succ(succ(zero()))).build().unwrap(),
    )
    .unwrap();
}

#[test]
fn proof_irrelevance() {
    let mut e = env();
    e.add_axiom("P", &[], prop().build().unwrap()).unwrap();
    e.add_axiom("p", &[], c("P").build().unwrap()).unwrap();
    e.add_axiom("q", &[], c("P").build().unwrap()).unwrap();
    let ty = app_(cl("Eq", vec![Level::zero()]), vec![c("P"), c("p"), c("q")]);
    e.add_def(
        "pq",
        &[],
        ty.build().unwrap(),
        app_(cl("Eq.refl", vec![Level::zero()]), vec![c("P"), c("p")])
            .build()
            .unwrap(),
    )
    .unwrap();
}

#[test]
fn eta_for_functions() {
    let mut e = env();
    // (fun x => Nat.succ x) = Nat.succ
    let f = arrow(nat(), nat());
    let ty = app_(
        cl("Eq", vec![Level::of_nat(1)]),
        vec![f.clone(), lam_("x", nat(), succ(v("x"))), c("Nat.succ")],
    );
    let val = app_(
        cl("Eq.refl", vec![Level::of_nat(1)]),
        vec![f, c("Nat.succ")],
    );
    e.add_def("eta", &[], ty.build().unwrap(), val.build().unwrap())
        .unwrap();
}

// ---- quantities ----

#[test]
fn linear_identity_is_accepted() {
    let mut e = env();
    let ty = pi_m(Mult::One, "x", nat(), nat());
    e.add_def(
        "id1",
        &[],
        ty.build().unwrap(),
        lam_m(Mult::One, "x", nat(), v("x")).build().unwrap(),
    )
    .unwrap();
}

#[test]
fn linear_duplication_is_rejected() {
    let mut e = env();
    let ty = pi_m(Mult::One, "x", nat(), nat());
    let val = lam_m(Mult::One, "x", nat(), add(v("x"), v("x")));
    let err = e
        .add_def("dup", &[], ty.build().unwrap(), val.build().unwrap())
        .unwrap_err();
    assert!(err.0.contains("multiplicity"), "{err}");
}

#[test]
fn linear_dropped_is_rejected() {
    let mut e = env();
    let ty = pi_m(Mult::One, "x", nat(), nat());
    let val = lam_m(Mult::One, "x", nat(), zero());
    let err = e
        .add_def("drop", &[], ty.build().unwrap(), val.build().unwrap())
        .unwrap_err();
    assert!(err.0.contains("multiplicity"), "{err}");
}

#[test]
fn linear_passed_to_unrestricted_parameter_is_rejected() {
    let mut e = env();
    // Nat.succ takes an unrestricted argument, so a linear variable cannot be passed to it
    let ty = pi_m(Mult::One, "x", nat(), nat());
    let val = lam_m(Mult::One, "x", nat(), succ(v("x")));
    assert!(e
        .add_def("bad", &[], ty.build().unwrap(), val.build().unwrap())
        .is_err());
}

#[test]
fn linear_constructor_field_consumes_linear_value() {
    let mut e = env();
    e.add_inductive(InductiveDecl {
        name: "LNat".into(),
        lparams: vec![],
        nparams: 0,
        ty: type_().build().unwrap(),
        ctors: vec![
            ("LNat.z".into(), c("LNat").build().unwrap()),
            (
                "LNat.s".into(),
                pi_m(Mult::One, "n", c("LNat"), c("LNat")).build().unwrap(),
            ),
        ],
    })
    .unwrap();
    let ty = pi_m(Mult::One, "x", c("LNat"), c("LNat"));
    let val = lam_m(Mult::One, "x", c("LNat"), app_(c("LNat.s"), vec![v("x")]));
    e.add_def("lsucc", &[], ty.build().unwrap(), val.build().unwrap())
        .unwrap();
}

#[test]
fn erased_binder_may_appear_in_types_only() {
    let mut e = env();
    // fun (A :0 Type) (x : A) => x   -- A is only used in a type
    let ty = pi_m(Mult::Zero, "A", type_(), arrow(v("A"), v("A")));
    let val = lam_m(Mult::Zero, "A", type_(), lam_("x", v("A"), v("x")));
    e.add_def("idA", &[], ty.build().unwrap(), val.build().unwrap())
        .unwrap();
    // fun (x :0 Nat) => x   -- runtime use of an erased variable
    let ty = pi_m(Mult::Zero, "x", nat(), nat());
    let val = lam_m(Mult::Zero, "x", nat(), v("x"));
    let err = e
        .add_def("leak", &[], ty.build().unwrap(), val.build().unwrap())
        .unwrap_err();
    assert!(err.0.contains("multiplicity"), "{err}");
}

#[test]
fn duplicate_declaration_is_rejected() {
    let mut e = env();
    assert!(e.add_axiom("Nat", &[], type_().build().unwrap()).is_err());
}

// ---- substitution ----

#[test]
fn instantiate_shifts_open_values_under_binders() {
    use apex_kernel::term::{bvar, instantiate, lam, sort};
    // `fun _ => #1`: the body refers to the outer variable #0
    let t = lam(Mult::Omega, sort(Level::zero()), bvar(1));
    // substituting an open value `#5` must shift it past the binder: `fun _ => #6`
    let r = instantiate(&t, &bvar(5));
    assert_eq!(r, lam(Mult::Omega, sort(Level::zero()), bvar(6)));
    // a closed value is unchanged by the shift
    let c = apex_kernel::term::cnst("X".into(), vec![]);
    assert_eq!(
        instantiate(&t, &c),
        lam(Mult::Omega, sort(Level::zero()), c)
    );
}

#[test]
fn mutual_tree_forest_recursion_reduces() {
    use apex_kernel::{MutualDecl, TypeDecl};
    let mut e = env();
    let ty = || c("Tree");
    let fo = || c("Forest");
    e.add_mutual(MutualDecl {
        lparams: vec![],
        nparams: 0,
        types: vec![
            TypeDecl {
                name: "Tree".into(),
                ty: type_().build().unwrap(),
                ctors: vec![("Tree.node".into(), arrow(fo(), ty()).build().unwrap())],
            },
            TypeDecl {
                name: "Forest".into(),
                ty: type_().build().unwrap(),
                ctors: vec![
                    ("Forest.nil".into(), fo().build().unwrap()),
                    (
                        "Forest.cons".into(),
                        arrow(ty(), arrow(fo(), fo())).build().unwrap(),
                    ),
                ],
            },
        ],
    })
    .unwrap();
    // size : Tree → Nat, counting nodes, by the recursor of Tree (motives for both types)
    let motive = |t: Raw| lam_("_", t, nat());
    let size = app_(
        cl("Tree.rec", vec![Level::of_nat(1)]),
        vec![
            motive(ty()),
            motive(fo()),
            lam_("f", fo(), lam_("ih", nat(), succ(v("ih")))),
            zero(),
            lam_(
                "t",
                ty(),
                lam_(
                    "f",
                    fo(),
                    lam_("iht", nat(), lam_("ihf", nat(), add(v("iht"), v("ihf")))),
                ),
            ),
        ],
    );
    let leaf = app_(c("Tree.node"), vec![c("Forest.nil")]);
    let two = app_(
        c("Tree.node"),
        vec![app_(c("Forest.cons"), vec![leaf, c("Forest.nil")])],
    );
    e.add_def(
        "size_two",
        &[],
        eq_nat(app_(size, vec![two]), succ(succ(zero())))
            .build()
            .unwrap(),
        refl_nat(succ(succ(zero()))).build().unwrap(),
    )
    .unwrap();
}
