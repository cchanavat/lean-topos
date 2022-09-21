/-
Copyright (c) 2022 Mathieu Chanavat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Chanavat
-/
import category_theory.limits.shapes.finite_limits
import category_theory.closed.cartesian
import category_theory.subobject.basic

import order.heyting.basic


/-!
# Subobject classifier for elementary topos

Useful api to work wiht pullback inside a topos
-/

open category_theory category_theory.category category_theory.limits 

universes v u

noncomputable theory

variables {C : Type u} [category.{v} C] [has_terminal.{v} C] 

variables {U X Y : C}

structure classifying_pullback (truth : ⊤_ C ⟶ Y) (f : U ⟶ X) (χ : X ⟶ Y)  :=
(comm : f ≫ χ = (terminal.from U) ≫ truth)
(is_pb : is_limit (pullback_cone.mk _ _ comm))

attribute [reassoc] classifying_pullback.comm

abbreviation classifying {Ω U X : C} (truth : ⊤_ C ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) := classifying_pullback truth f χ 

structure is_subobject_classifier {Ω : C} (truth : ⊤_ C ⟶ Ω) :=
(classifier_of : ∀ {U X} (f : U ⟶ X) [mono.{v} f], X ⟶ Ω)
(classifies' : ∀ {U X} (f : U ⟶ X) [mono f], classifying truth f (classifier_of f))
(uniquely' : ∀ {U X} (f : U ⟶ X) [mono f] (χ₁ : X ⟶ Ω), classifying truth f χ₁ → classifier_of f = χ₁)

variable (C)

/--
A category has a subobject classifier if there is a monomorphism `truth` which is a
subobject classifier.
-/
class has_subobject_classifier :=
(Ω : C)
(truth : ⊤_ C ⟶ Ω)
[truth_mono : mono.{v} truth]
(is_subobj_classifier : is_subobject_classifier truth)

variables [has_subobject_classifier.{v} C]

/-! Convenience interface to the `has_subobject_classifier` class. -/
namespace classifier

/-- Convenience notation for the classifier target given the typeclass `has_subobject_classifier`. -/
def Ω : C := has_subobject_classifier.Ω.{v}
/-- Convenience notation for the classifier given the typeclass `has_subobject_classifier`. -/
def truth : ⊤_ C ⟶ Ω C := has_subobject_classifier.truth
/-- From the typeclass `has_subobject_classifier`, show that the classifier `truth` is a monomorphism. -/
instance truth_mono : mono (truth C) := has_subobject_classifier.truth_mono
/-- The subobject classifier given by `has_subobject_classifier` is actually a classifier. -/
def subobj_classifier_is_subobj_classifier : is_subobject_classifier (truth C) := has_subobject_classifier.is_subobj_classifier

variable {C}
def classifier_of {U X : C} (f : U ⟶ X) [mono f] : X ⟶ Ω C :=
(subobj_classifier_is_subobj_classifier C).classifier_of f
def classifies {U X : C} (f : U ⟶ X) [mono f] : classifying (truth C) f (classifier_of f) :=
(subobj_classifier_is_subobj_classifier C).classifies' f
lemma uniquely {U X : C} (f : U ⟶ X) [mono f] (χ₁ : X ⟶ Ω C) (hχ : classifying (truth C) f χ₁) : classifier_of f = χ₁ :=
(subobj_classifier_is_subobj_classifier C).uniquely' f χ₁ hχ
 
end classifier

/- If we have σ : X → Ω then we have the following pullback, we call { σ } the canonical subobject
  { σ } -> ⊤
    |      |
    X ---> Ω 
-/

variable {C}
notation `s{` σ `}s` := pullback σ (classifier.truth _)

open classifier

abbreviation canonical_incl {X : C} [has_pullbacks C] (σ : X ⟶ Ω C) : s{ σ }s ⟶ X := pullback.fst
def canonical_incl_of_mono {X Y : C} [has_pullbacks C] (m : X ⟶ Y) [mono m] : 
  s{ classifier_of m }s ⟶ Y :=
canonical_incl (classifier_of m)

instance canonical_incl_mono {X : C} [has_pullbacks C] (σ : X ⟶ Ω C) : 
  mono (canonical_incl σ) := 
pullback.fst_of_mono.

lemma pb_condition_canonical_inclusion {X : C} [has_pullbacks C] (σ : X ⟶ Ω C) :
  canonical_incl σ ≫ σ = terminal.from s{ σ }s ≫ truth C :=
begin
  convert pullback.condition
end

abbreviation to_sub {X : C} [has_pullbacks C] (σ : X ⟶ Ω C) : subobject X := subobject.mk (canonical_incl σ)

/- The truth classifies the identity -/

variable (C)

lemma terminal_from_self_is_id : terminal.from (⊤_ C) = 𝟙 (⊤_ C) := 
is_terminal.from_self terminal_is_terminal

lemma truth_classifies_id : classifying (truth C) (𝟙 (⊤_ C)) (truth C) := 
{ comm := by rw (terminal_from_self_is_id ),
  is_pb := 
  begin
    conv in (terminal.from (⊤_ C)) {rw terminal_from_self_is_id },
    exact pullback_cone.is_limit_mk_id_id (truth C)
  end
}

lemma truth_classifies_id.comm : 𝟙 (⊤_ C) ≫ (truth C) = 𝟙 (⊤_ C) ≫ (truth C) := by simp
lemma truth_classifies_id.is_pb : 
  is_limit (pullback_cone.mk (𝟙 (⊤_ C)) (𝟙 (⊤_ C)) (truth_classifies_id.comm C)) :=
begin 
  have h := (truth_classifies_id C).is_pb,
  conv at h in (terminal.from (⊤_ C)) {rw terminal_from_self_is_id},
  assumption
end
