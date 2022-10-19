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


variable (X : C)

def sub_to_hom : subobject X → (X ⟶ Ω C) := λ s, classifier_of s.arrow
def hom_to_sub : (X ⟶ Ω C) → subobject X := λ σ, canonical_sub σ

lemma sub_equiv_hom : subobject X ≃ (X ⟶ Ω C) := 
{ to_fun := sub_to_hom X,
  inv_fun := hom_to_sub X,
  left_inv := λ S, sub_eq_canonical_sub_of_classifier S,  
  right_inv := λ σ, classifier.uniquely _ _ 
                   (classifying_pullback.mk _ (is_pullback_canonical_arrow _)) }

