struct Animal { legs: Nat }
struct Dog extends Animal { name: String }
struct Generic<T> { val: T }
struct Tagged<T> extends Generic<T> { tag: Nat }

theorem inherited(d: Dog): d.legs = d.toAnimal().legs := rfl
theorem build(): Dog.mk(4, "rex").legs = 4 := rfl
theorem tagged<T: Type>(t: Tagged<T>): Tagged.mk(t.val, t.tag) = t := rfl
