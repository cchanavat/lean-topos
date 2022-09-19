import category_theory.closed.cartesian

import subobject_classifier

open category_theory category_theory.limits classifier


/-!
# Topos

Basic defintion of a topos

-/

universes v u

noncomputable theory

variables (C : Type u) [category.{v} C] 

class topos :=
[lim : has_finite_limits.{v} C]
[sub : has_subobject_classifier.{v} C]
[cc : cartesian_closed.{v} C]

attribute [instance] topos.lim topos.sub topos.cc

/- true_X from McLane -/
variables {C} [topos.{v} C]

abbreviation lift_truth (X : C) : X ⟶ Ω C := terminal.from X ≫ truth C
