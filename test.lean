import category_theory.limits.types

open category_theory category_theory.limits functor

universes u

local attribute [-instance]
  limits.has_kernel_pair_of_mono

example {X Y : Type u} (m : X ⟶ Y) : has_pullback m m := infer_instance
