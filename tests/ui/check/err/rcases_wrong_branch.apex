// expect: unknown identifier
theorem bad2<P: Prop, Q: Prop>(h: P \/ Q): P := by { rcases h with p | q; exact p; exact p }
