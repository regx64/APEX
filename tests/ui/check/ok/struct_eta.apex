struct Point { x: Nat, y: Nat }

// structure eta: a structure value equals the constructor applied to its projections
theorem eta_point(p: Point): p = Point.mk(p.x, p.y) := rfl
theorem eta_symm(p: Point): Point.mk(p.x, p.y) = p := rfl
theorem proj_x(a: Nat, b: Nat): Point.mk(a, b).x = a := rfl

struct Wrap<T> { val: T }
theorem eta_wrap<T: Type>(w: Wrap<T>): w = Wrap.mk(w.val) := rfl

theorem eta_prod<A: Type, B: Type>(p: Prod<A, B>): p = Prod.mk(p.fst, p.snd) := rfl
