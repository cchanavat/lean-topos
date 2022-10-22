import category_theory.limits.shapes
import category_theory.limits.preserves.limits

import subobject_classifier

/-!
# Pullbacks inside a topos

Lemmas to work with pullbacks in topos
-/
/-
  Convention (compatible with mathlib)
  
  pullback_cone f g
  pullback_cone.mk fst snd

  X -snd-> Y
  |        |
 fst       g
  |        |
  Z --f--> W
-/

open category_theory category_theory.category category_theory.limits classifier

noncomputable theory
universes u v
variables {C : Type u} [category.{v} C] [has_finite_limits C] [has_subobject_classifier C]


lemma pb_classifier_condition {X Y : C} (m : X ⟶ Y) [mono m] : 
  m ≫ classifier_of m = lift_truth X := 
begin
  rw (classifies m).comm, 
end

/- Useful lemmas about pb -/
variables {X Y : C} (m : X ⟶ Y) [mono m]

def monic_to_pb_cone : pullback_cone (truth C) (classifier_of m) :=
pullback_cone.mk (terminal.from _) m (classifier.comm _).symm

def sub_iso_cano : X ≅ s{ classifier_of m }s := 
  (limit.iso_limit_cone (limit_cone.mk _ (classifies m).is_pb)).symm

/- Given
       X ---> ⊤
       |      |
  W -> Y ---> Ω 
    h
  and the appropriate commutation, we lift it to a map W -> X,
  and we prove the commutativity of the triangle W X Y, and the uniqueness

-/
def pb_lift_from_monic {W X Y : C} (m : X ⟶ Y) [mono m] (h : W ⟶ Y)  
  (w : h ≫ (classifier_of m) = lift_truth _) := 
pullback_cone.is_limit.lift' (classifies m).is_pb h (terminal.from W) w

def pb_lift_from_monic.map {W X Y : C} (m : X ⟶ Y) [mono m] (h : W ⟶ Y)  
  (w : h ≫ (classifier_of m) = lift_truth _) : 
  W ⟶ X := 
(pb_lift_from_monic m h w).1

lemma pb_lift_from_monic.comm {W X Y : C} (m : X ⟶ Y) [mono m] (h : W ⟶ Y)  
  (w : h ≫ (classifier_of m) = lift_truth _) : 
  (pb_lift_from_monic.map m h w) ≫ m = h := 
(pb_lift_from_monic m h w).2.left

lemma pb_lift_from_monic.unique {W X Y : C} (m : X ⟶ Y) [mono m] (h : W ⟶ Y)  
  (w : h ≫ (classifier_of m) = lift_truth _) : 
  ∀ u : W ⟶ X, u ≫ m = h → u = pb_lift_from_monic.map m h w := 
begin
  intros u h1,
  have h :=
  calc 
  u ≫ m = h                                   : by assumption
  ...    = (pb_lift_from_monic.map m h w) ≫ m : by symmetry; apply pb_lift_from_monic.comm,
  rw ←cancel_mono m, assumption
end
