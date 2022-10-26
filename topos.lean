import category_theory.isomorphism
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.reflexive
import category_theory.limits.opposites
import category_theory.closed.cartesian
import category_theory.adjunction.basic
import category_theory.functor.epi_mono
import category_theory.monad.basic
import category_theory.monad.monadicity

import subobject_classifier
import adjunction
import image

open category_theory category_theory.category category_theory.limits category_theory.cartesian_closed classifier opposite 


/-!
# Topos

Basic definitions of a topos
From Sheaves IV
-/

universes v u

noncomputable theory

variables (C : Type u) [category.{v} C] 

class topos :=
[lim : has_finite_limits.{v} C]
[sub : has_subobject_classifier.{v} C]
[cc : cartesian_closed.{v} C]

attribute [instance] topos.lim topos.sub topos.cc


variables [topos C]

-- It doesn't seem to bee infered automatically
instance : has_finite_colimits Cᵒᵖ := has_finite_colimits_opposite

variables {C} (c : C)

def sub_to_hom : subobject c → (c ⟶ Ω C) := λ s, classifier_of s.arrow
def hom_to_sub : (c ⟶ Ω C) → subobject c := λ σ, canonical_sub σ

lemma sub_equiv_hom : subobject c ≃ (c ⟶ Ω C) := 
{ to_fun := sub_to_hom c,
  inv_fun := hom_to_sub c,
  left_inv := λ S, sub_eq_canonical_sub_of_classifier S,  
  right_inv := λ σ, classifier.uniquely _ _ 
                   (classifying_pullback.mk _ (is_pullback_canonical_arrow _)) }

def δ := classifier_of (diag c)
def singleton_map := curry (δ c)

variables (C) {a b : C}

def P : Cᵒᵖ ⥤ C := {
  obj := λ c, (exp c.unop).obj (Ω C),
  map := λ c d f, (pre f.unop).app (Ω C),
  map_id' := λ c, by {rw [unop_id, pre_id, nat_trans.id_app]},
  map_comp' := λ _ _ _ f g, by {rw [unop_comp, pre_map, nat_trans.comp_app]} }

def P_op : C ⥤ Cᵒᵖ := functor.right_op (P C) 

variable {C}

def in_map : c ⨯ (P C).obj (op c) ⟶ Ω C := (exp.ev c).app (Ω C)  

variable {c}

lemma in_map_natural (g : a ⟶ (P C).obj (op b)) :
  uncurry g = limits.prod.map (𝟙 _) g ≫ in_map b := uncurry_eq g

lemma in_map_dinatural (h : b ⟶ c) : 
  limits.prod.map h (𝟙 _) ≫ in_map c = limits.prod.map (𝟙 _) ((P C).map h.op) ≫ in_map b :=
begin
  erw [←in_map_natural, uncurry_pre], 
  refl
end

variables {C c} {d : C} {f : c ⟶ d}

namespace delta 

open category_theory.limits.prod

def pullback_cone_map_diag (f : c ⟶ d) : pullback_cone (map f (𝟙 _)) (diag d) :=
pullback_cone.mk (lift (𝟙 _) f) f (by simp only [lift_map,comp_lift, id_comp, comp_id])

lemma cone_map_diag_fst (s : pullback_cone (map f (𝟙 _)) (diag d)) : s.fst ≫ fst ≫ f = s.snd :=
by { rw [←map_fst f (𝟙 _), ←assoc, s.condition, assoc, lift_fst, comp_id] }

lemma cone_map_diag_snd (s : pullback_cone (map f (𝟙 _)) (diag d)) : s.fst ≫ snd = s.snd :=
by { rw [←comp_id (s.fst ≫ snd), assoc, ←map_snd f (𝟙 _), 
         ←assoc, s.condition, assoc, lift_snd, comp_id] }

lemma cone_map_diag_fst_snd (s : pullback_cone (map f (𝟙 _)) (diag d)) : 
  s.fst ≫ fst ≫ f = s.fst ≫ snd := eq.trans (cone_map_diag_fst s) (cone_map_diag_snd s).symm

def is_limit_pullback_cone_map_diag : is_limit (pullback_cone_map_diag f) :=
begin
  apply pullback_cone.is_limit.mk (pullback_cone_map_diag f).condition (λ s, s.fst ≫ fst); 
  intro s,
  { simp only [assoc], dunfold pullback_cone_map_diag, rw pullback_cone.mk_fst,
    rw [comp_lift], nth_rewrite 1 ←comp_id s.fst, simp only [comp_id],
    apply hom_ext,
      rw [assoc, lift_fst, ←assoc, comp_id (s.fst ≫ fst)],
      rw [assoc, lift_snd], apply cone_map_diag_fst_snd },
  { simp only [assoc], erw pullback_cone.mk_snd, apply cone_map_diag_fst, },
  { intros l fst' snd', simp only, 
    rw ←eq_whisker fst' fst, erw [assoc, lift_fst, comp_id] }
end

variable (f)

def big_square_cone : pullback_cone (map f (𝟙 d) ≫ δ d) (truth C) :=
pullback_cone.mk (lift (𝟙 c) f) (f ≫ terminal.from d) 
(by { erw [←assoc, (pullback_cone_map_diag f).condition, assoc, classifier.comm (diag d),
      ←assoc, terminal.comp_from] })

lemma is_limit_big_square_cone : is_limit (big_square_cone f) :=
begin
  apply big_square_is_pullback f (terminal.from _) (map f (𝟙 _)) (δ _) 
    (lift (𝟙 _) f) (diag _) (truth C),
  apply classifier.is_pb,
  apply is_limit_pullback_cone_map_diag,
end

lemma big_square_classifying : classifying (truth C) (lift (𝟙 c) f) (map f (𝟙 d) ≫ δ d) := 
{ comm := by { rw ←terminal.comp_from f, erw (big_square_cone f).condition, refl },
  is_pb := 
  begin
    let g := is_limit_big_square_cone f, unfold big_square_cone at g,
    simp [terminal.comp_from f] at g, assumption,
  end }

lemma classifies : classifier_of (lift (𝟙 _) f) = map f (𝟙 _) ≫ δ d :=
classifier.uniquely _ _ (big_square_classifying f)

variable (g : c ⟶ d)

lemma cancel_classifier:  (classifier_of (lift (𝟙 _) f) =  classifier_of (lift (𝟙 _) g)) ↔ f = g :=
begin
  split; intro heq,
  { have k := (pullback_cone.is_limit.lift' (classifier.is_pb (lift (𝟙 _) f)) 
    ((lift (𝟙 _) g)) (terminal.from _) (by rw [heq, classifier.comm])).prop.left,
    have eq_id := eq_whisker k fst,
    erw [assoc, lift_fst, lift_fst, comp_id] at eq_id,
    rw [eq_id, id_comp] at k,
    convert eq_whisker k snd,
    erw lift_snd, rw lift_snd },
  { rw heq }
end

end delta

-- We show that a topos is balanced
namespace balanced

lemma iso_of_is_limit_fork_id {f : c ⟶ d} {s : fork f f} (is_lim : is_limit s) : is_iso s.ι :=
begin
  apply is_iso.mk,
  use is_lim.lift (fork.of_ι (𝟙 c) (by simp)),
  split,
  { apply fork.is_limit.hom_ext is_lim,
    rw [assoc, fork.is_limit.lift_ι, fork.ι_of_ι, id_comp],
    apply comp_id },
  { apply fork.is_limit.lift_ι }
end

lemma is_limit_of_is_limit_fork_eq {f g : c ⟶ d} {s : fork f g} (is_lim : is_limit s) (heq : f = g) : 
  is_limit (fork.of_ι s.ι (by rw s.condition) : fork f f) :=
begin
  refine fork.is_limit.mk _ 
    (λ t : fork f f, (fork.is_limit.lift' is_lim t.ι (by rw ←heq)).val) _ _; 
  intro t,
  { apply fork.is_limit.lift_ι },
  { intros r ht, apply fork.is_limit.hom_ext is_lim, erw fork.is_limit.lift_ι, apply ht }
end

lemma iso_of_is_limit_fork_eq {f g : c ⟶ d} {s : fork f g} (is_lim : is_limit s) (heq : f = g) : 
  is_iso s.ι := iso_of_is_limit_fork_id (is_limit_of_is_limit_fork_eq is_lim heq)

variable (C)

instance topos_balanced : balanced C :=
{ is_iso_of_mono_of_epi := λ c d f m e,
  begin
    resetI,
    apply iso_of_is_limit_fork_eq (image.monic_is_limit_fork f),
    rw ←cancel_epi f,
    exact (image.monic_to_canonical_fork f).condition
  end }

end balanced
