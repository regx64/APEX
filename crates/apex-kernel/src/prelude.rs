//! Bootstrap declarations written directly against the kernel.

use crate::builder::*;
use crate::env::{Env, KResult};
use crate::inductive::InductiveDecl;
use crate::level::Level;

/// `Eq`, `Nat`, `Nat.add` and `List`.
pub fn add_prelude(env: &mut Env) -> KResult<()> {
    let u = Level::param("u");

    // inductive Eq.{u} {α : Sort u} (a : α) : α → Prop | refl : Eq a a
    env.add_inductive(InductiveDecl {
        name: "Eq".into(),
        lparams: vec!["u".into()],
        nparams: 2,
        ty: pi_(
            "α",
            sort_(u.clone()),
            pi_("a", v("α"), arrow(v("α"), prop())),
        )
        .build()?,
        ctors: vec![(
            "Eq.refl".into(),
            pi_(
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

    // inductive List.{u} (α : Type u) : Type u | nil | cons (head : α) (tail : List α)
    let tu = || sort_(u.clone().succ());
    let list_a = || app_(cl("List", vec![u.clone()]), vec![v("α")]);
    env.add_inductive(InductiveDecl {
        name: "List".into(),
        lparams: vec!["u".into()],
        nparams: 1,
        ty: pi_("α", tu(), tu()).build()?,
        ctors: vec![
            ("List.nil".into(), pi_("α", tu(), list_a()).build()?),
            (
                "List.cons".into(),
                pi_("α", tu(), arrow(v("α"), arrow(list_a(), list_a()))).build()?,
            ),
        ],
    })?;
    Ok(())
}
