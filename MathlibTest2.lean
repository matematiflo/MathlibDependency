import Mathlib.Algebra.Group.Defs

example [Group G] : (1 : G) * 1 = 1 := by exact one_mul 1

example : 1 + 1 = 2 := refl 2
example : 1 + 1 = 2 := refl (1 +1)
example : 1 + 1 = 2 := rfl  -- same as `refl 2`, with the argument taken implicitly

example : 1 + 1 = 2 := by {exact refl 2}  -- in tactic mode
example : 1 + 1 = 2 := by rfl  -- in tactic mode
