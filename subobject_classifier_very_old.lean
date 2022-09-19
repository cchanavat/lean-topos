import pullbacks

universes v u v₂ u₂

open category_theory category_theory.category category_theory.limits 

variables {C : Type u} [category.{v} C]

/-- Define what it means for χ to classify the mono f. -/
abbreviation classifying {Ω Ω₀ U X : C} (truth : Ω₀ ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) := has_pullback_top f χ truth
/--
`is_subobject_classifier truth` holds if the morphism `truth : Ω₀ ⟶ Ω` is a subobject classifier,
i.e. that for any monomorphism `U ⟶ X`, there is a unique morphism `X ⟶ Ω` forming a pullback
square.
Note we do not require `truth` to be a monomorphism here, nor that `Ω₀` is terminal.
-/
structure is_subobject_classifier {Ω Ω₀ : C} (truth : Ω₀ ⟶ Ω) :=
(classifier_of : ∀ {U X} (f : U ⟶ X) [mono.{v} f], X ⟶ Ω)
(classifies' : ∀ {U X} (f : U ⟶ X) [mono f], classifying truth f (classifier_of f))
(uniquely' : ∀ {U X} (f : U ⟶ X) [mono f] (χ₁ : X ⟶ Ω), classifying truth f χ₁ → classifier_of f = χ₁)

variable (C)

/--
A category has a subobject classifier if there is a monomorphism `truth` which is a
subobject classifier.
We do not require `Ω₀` to be terminal, nor do we assume the existence of any limits.
-/
class has_subobject_classifier :=
(Ω Ω₀ : C)
(truth : Ω₀ ⟶ Ω)
[truth_mono : mono.{v} truth]
(is_subobj_classifier : is_subobject_classifier truth)

variables [has_subobject_classifier.{v} C]

/-! Convenience interface to the `has_subobject_classifier` class. -/
namespace classifier

/-- Convenience notation for the classifier target given the typeclass `has_subobject_classifier`. -/
def Ω : C := has_subobject_classifier.Ω.{v}
/-- Convenience notation for the classifier source given the typeclass `has_subobject_classifier`. -/
def Ω₀ : C := has_subobject_classifier.Ω₀.{v}
/-- Convenience notation for the classifier given the typeclass `has_subobject_classifier`. -/
def truth : Ω₀ C ⟶ Ω C := has_subobject_classifier.truth
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

instance unique_to_Ω₀ (X : C) : unique (X ⟶ Ω₀ C) := {
  default := (classifies (𝟙 X)).top,
  uniq := begin
  intros, 
  rw [← cancel_mono (truth C), (classifies (𝟙 X)).comm, id_comp, uniquely],
  let comm : a ≫ truth C = 𝟙 X ≫ (a ≫ truth C) := by simp,
  let pb_cone := pullback_cone.mk a (𝟙 X) comm,
  suffices h : is_limit (pullback_cone.mk a (𝟙 X) comm),
  { apply has_pullback_top_of_is_pb h },
  { apply is_limit.mk' pb_cone,
    intros, refine ⟨ s.snd , _ ⟩,
    { split, simp, rw [← cancel_mono (truth C), s.condition], simp,
      split, simp, rw comp_id s.snd,
      intros m h1 h2, simp at h2, rw ← h2,symmetry, apply comp_id } },
  end
}

def Ω₀_terminal : is_terminal (Ω₀ C) := is_terminal.of_unique (Ω₀ C).
 
end classifier

