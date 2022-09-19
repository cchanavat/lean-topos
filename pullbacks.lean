import category_theory.limits.shapes
import category_theory.limits.preserves.limits

import subobject_classifier
import topos
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

open category_theory category_theory.category category_theory.limits classifier topos

noncomputable theory
universes u v
variables {C : Type u} [category.{v} C] [topos.{v} C]


@[simp] lemma pb_classifier_condition {X Y : C} (m : X ⟶ Y) [mono m] : 
  m ≫ classifier_of m = lift_truth X := 
begin
  rw (classifies m).comm,
end

/- Useful lemmas about pb -/
variables {X Y : C} (m : X ⟶ Y) [mono m]

def monic_to_pb_cone : pullback_cone (truth C) (classifier_of m) :=
pullback_cone.mk (terminal.from _) m (by simp)

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


variables {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)
variables (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)
variables (h₁ : f₁ ≫ i₂ = i₁ ≫ g₁) (h₂ : f₂ ≫ i₃ = i₂ ≫ g₂)



-- def big_square_is_pullback' (H : is_limit (pullback_cone.mk _ _ h₂))
--   (H' : is_limit (pullback_cone.mk _ _ h₁)) : is_limit (pullback_cone.mk _ _ (show (f₁ ≫ f₂) ≫ i₃ = i₁ ≫ g₁ ≫ g₂,
--       by rw [← category.assoc, ←h₁, category.assoc, h₂, category.assoc])) :=
-- begin
--   have Hsymm : is_limit (pullback_cone.mk _ _ h₁.symm) := sorry, --is_limit.of_iso_limit H' (pullback_symmetry _ _) ,
--   have H'symm : is_limit (pullback_cone.mk _ _ h₂.symm) := sorry,
--   sorry, -- exact big_square_is_pullback f₁ f₂ g₁ g₂ i₁ i₂ i₃ h₁.symm h₂.symm H'symm Hsymm 
-- end
-- #check big_square_is_pullback'