import pullbacks

universes v u v₂ u₂

open category_theory category_theory.category category_theory.limits 

variables {C : Type u} [category.{v} C] [has_finite_limits C]

/-- Define what it means for χ to classify the mono f. -/
abbreviation classifying {Ω U X : C} (truth : ⊤_ C ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) := has_pullback_top f χ truth

/--
`is_subobject_classifier truth` holds if the morphism `truth : ⊤_ ⟶ Ω` is a subobject classifier,
i.e. that for any monomorphism `U ⟶ X`, there is a unique morphism `X ⟶ Ω` forming a pullback
square.
Note we do not require `truth` to be a monomorphism here.
-/
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

