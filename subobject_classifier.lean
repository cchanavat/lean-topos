/-
Copyright (c) 2022 Clémence Chanavat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clémence Chanavat
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
 
lemma classifier.comm {U X : C} (f : U ⟶ X) [mono f] : 
  f ≫ (classifier_of f) = terminal.from _ ≫ truth C :=
classifying_pullback.comm (classifies _)

lemma classifier.is_pb {U X : C} (f : U ⟶ X) [mono f] :
  is_limit (pullback_cone.mk _ _ (classifier.comm f)) := classifying_pullback.is_pb (classifies _)

end classifier

/- If we have σ : X → Ω then we have the following pullback, we call { σ } the canonical subobject
  { σ } -> ⊤
    |      |
    X ---> Ω 
-/

variable {C}
notation `s{` σ `}s` := pullback σ (classifier.truth _)



open classifier


/- true_X from McLane -/
abbreviation lift_truth (X : C) : X ⟶ Ω C := terminal.from X ≫ truth C

abbreviation canonical_incl {X : C} [has_pullbacks C] (σ : X ⟶ Ω C) : s{ σ }s ⟶ X := pullback.fst

def canonical_incl_of_mono {X Y : C} [has_pullbacks C] (m : X ⟶ Y) [mono m] : 
  s{ classifier_of m }s ⟶ Y :=
canonical_incl (classifier_of m)

variables [has_pullbacks C] (σ : X ⟶ Ω C)

instance canonical_incl_mono : mono (canonical_incl σ) := pullback.fst_of_mono

lemma canonical_incl_comm : canonical_incl σ ≫ σ = terminal.from s{ σ }s ≫ truth C :=
begin
  convert pullback.condition
end

abbreviation canonical_sub : subobject X := subobject.mk (canonical_incl σ)

def canonical_sub_iso_canonical : ↑(canonical_sub σ) ≅ s{ σ }s :=
begin
  apply subobject.iso_of_eq_mk _ (canonical_incl σ), refl
end

def canonical_iso_canonical_sub : s{ σ }s ≅ ↑(canonical_sub σ) := 
(canonical_sub_iso_canonical σ).symm

lemma sub_eq_canonical_sub_of_classifier (S : subobject X) : 
  canonical_sub (classifier_of S.arrow) = S :=
begin
  ext1,
  exact is_limit.cone_point_unique_up_to_iso_hom_comp 
    (pullback_is_pullback _ _) (classifier.is_pb S.arrow) walking_cospan.left
end

def pb_cone_of_canonical_sub_arrow : pullback_cone σ (truth C) :=
pullback_cone.mk (canonical_sub σ).arrow (terminal.from _) 
(by { rw [←subobject.underlying_iso_hom_comp_eq_mk, assoc, 
          canonical_incl_comm, ←assoc, terminal.comp_from] })

lemma pb_cone_of_canonical_sub_arrow_X : 
  (pb_cone_of_canonical_sub_arrow σ).X = ↑(canonical_sub σ) := rfl

lemma is_pullback_canonical_arrow :
  is_limit (pb_cone_of_canonical_sub_arrow σ) :=
begin
  apply is_limit.of_iso_limit (pullback_is_pullback σ (truth C)),
  symmetry,
  refine pullback_cone.ext (subobject.underlying_iso (canonical_incl σ)) _ 
    (is_terminal.hom_ext (terminal_is_terminal) _ _),
  symmetry, rw [pullback_cone.mk_fst, subobject.underlying_iso_hom_comp_eq_mk], refl
end

lemma canonical_is_pullback : 
  is_limit (pullback_cone.mk (canonical_incl σ) (terminal.from _) (canonical_incl_comm σ)) :=
begin
 convert pullback_is_pullback _ _,
  apply is_terminal.hom_ext terminal_is_terminal,
end

lemma canonical_incl_classifies : classifying (truth C) (canonical_incl σ) σ :=
{ comm := canonical_incl_comm σ,
  is_pb := canonical_is_pullback σ }
 
@[simp] lemma classifier_of_canonical_incl_eq_self : classifier_of (canonical_incl σ) = σ :=
uniquely _ _ (canonical_incl_classifies σ)



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
