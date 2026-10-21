// expect: unsolved goals
theorem t<P: Prop, Q: Prop>(p: P): And<P, Q> := by { constructor; exact p }
