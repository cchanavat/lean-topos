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


namespace direct_image

open category_theory.limits.prod

variables {b' : C} (k : b' ⟶ b) [mono k]

def uncurried := classifier_of (canonical_incl (in_map b') ≫ map k (𝟙 _))

def curried : (P C).obj (op b') ⟶ (P C).obj (op b) := curry (uncurried k)

lemma curried_id : curried (𝟙 b) = 𝟙 ((P C).obj (op b)) :=
begin
  erw [curry_eq_iff, uncurry_id_eq_ev],
  unfold uncurried, simp only [map_id_id, comp_id],
  rw classifier_of_canonical_incl_eq_self, refl
end

variables {g : c ⟶ b} {k} 

lemma mono_of_pullback (s : pullback_cone g k) (is_lim : is_limit s) : mono s.fst := 
{ right_cancellation := 
  begin
    intros d u v heq,
    apply pullback_cone.is_limit.hom_ext is_lim heq,
    rw [←cancel_mono k, assoc, ←s.condition, ←assoc, heq, assoc, s.condition, assoc]
  end }
 
-- The instance mono s.fst should be infered from 
-- pullback.fst_of_mono but is not

-- We follow Sheaves IV.3.2, with mostly their notations
variables (s : pullback_cone g k) 

def upper_right_rectangle (k : b' ⟶ b) [mono k] : pullback_cone (uncurried k) (truth C) :=
pullback_cone.mk (canonical_incl (in_map b') ≫ map k (𝟙 _)) (terminal.from _) (classifier.comm _)

def upper_left_bottom : pullback_cone (map g (𝟙 ((P C).obj (op b')))) (map k (𝟙 ((P C).obj (op b')))) :=
pullback_cone.mk (map s.fst (𝟙 _)) (map s.snd (𝟙 _)) (by { rw [map_map, map_map, s.condition] })

def lower_right_rectangle [mono s.fst] : pullback_cone (uncurried s.fst) (truth C) := 
pullback_cone.mk (canonical_incl (in_map s.X) ≫ map s.fst (𝟙 _)) (terminal.from _) (classifier.comm _)

def lower_left_bottom : pullback_cone (map (𝟙 _) ((P C).map s.snd.op)) (map s.fst (𝟙 _)) :=
pullback_cone.mk (map s.fst (𝟙 _)) (map (𝟙 _) ((P C).map s.snd.op)) 
(by repeat { rw [map_map, id_comp, comp_id] }) 

lemma is_limit_upper_right_rectangle : is_limit (upper_right_rectangle k) :=
classifier.is_pb _

lemma is_limit_upper_left_bottom (is_lim : is_limit s) : is_limit (upper_left_bottom s) :=
is_pullback_of_prod_pullback is_lim (is_pullback_square_ids_snd _)

lemma is_limit_lower_right_rectangle [mono s.fst] : is_limit (lower_right_rectangle s) :=
classifier.is_pb _

lemma is_limit_lower_left_bottom (is_lim : is_limit s) : is_limit (lower_left_bottom s) :=
is_pullback_of_prod_pullback (is_pullback_square_ids_fst _) (is_pullback_square_ids_snd _)

def upper_big_canonical := canonical_incl (map s.snd (𝟙 _) ≫ in_map b')

-- def upper_left_top : pullback_cone (map s.snd (𝟙 _)) (canonical_incl (in_map b')) :=
--   pullback_cone.mk pullback.fst pullback.snd pullback.condition

-- def lower_left_top : pullback_cone (map (𝟙 s.X) ((P C).map s.snd.op)) (canonical_incl (in_map s.X)) :=
--   pullback_cone.mk pullback.fst pullback.snd pullback.condition

-- lemma upper_left_eq_lower_left_X : (upper_left_top s).X = (lower_left_top s).X :=
-- begin
--   erw [pullback_cone.mk_X],
-- end
namespace upper

-- def left := (pullback.fst :  pullback (map s.snd (𝟙 _) ≫ in_map b') (truth C) ⟶ s.X ⨯ (P C).obj (op b'))
def left := (pullback.fst : pullback (map s.snd (𝟙 _)) (canonical_incl (in_map b')) ⟶ s.X ⨯ (P C).obj (op b'))
def top := (pullback.snd : pullback (map s.snd (𝟙 _)) (canonical_incl (in_map b')) ⟶ s{in_map b'}s)

def lower_top : 
  pullback (map (𝟙 s.X) ((P C).map s.snd.op)) (canonical_incl (in_map s.X)) ⟶ s{in_map s.X}s := 
pullback.snd 


def cone : pullback_cone (map s.snd (𝟙 _) ≫ in_map b') (truth C) :=
pullback_cone.mk (left s) (top s ≫ terminal.from _)
begin
  erw [←assoc, pullback.condition], 
  rw [assoc, canonical_incl_comm, assoc], 
  refl,
end

lemma is_pullback_cone : is_limit (cone s) :=
big_square_is_pullback (top s) (terminal.from _)
    (map s.snd (𝟙 _)) (in_map b') (left s) (canonical_incl (in_map b')) (truth C)
    pullback.condition (canonical_incl_comm (in_map b')) 
    (canonical_is_pullback _) (pullback_is_pullback _ _)

def cone_lower : pullback_cone (map (𝟙 s.X) ((P C).map s.snd.op) ≫ in_map s.X) (truth C) :=
pullback_cone.mk (left s) (top s ≫ terminal.from _) 
begin
rw ←in_map_dinatural, exact (cone s).condition,
end

lemma is_pullback_cone_lower : is_limit (cone_lower s) :=
begin
  apply big_square_is_pullback (lower_top s) (terminal.from _)
    (map (𝟙 s.X) ((P C).map s.snd.op)) (in_map s.X) (left s) (canonical_incl (in_map s.X)) (truth C),
end
end upper

lemma uncurried_beck_chevalley [mono s.fst] :
  map g (𝟙 _) ≫ uncurried k = map (𝟙 _) ((P C).map s.snd.op) ≫ uncurried s.fst := 
begin
  sorry
end

lemma curried_beck_chevalley' [mono s.fst] :
  curried k ≫ (P C).map g.op = (P C).map s.snd.op ≫ curried s.fst := 
begin
  dunfold curried,
  have eq := congr_arg curry (uncurried_beck_chevalley s),
  rw curry_natural_left at eq,
  erw [←eq, eq_curry_iff, uncurry_natural_left, uncurry_pre],
  clear eq,
  erw [←assoc, map_map, id_comp, comp_id (curry (uncurried k))],
  rw [←comp_id g.op.unop, ←id_comp (curry (uncurried k)), ←map_map, assoc],
  rw [←uncurry_eq, uncurry_curry], refl,
end

variable {s}
def curried_beck_chevalley (is_lim : is_limit s) :=
  @curried_beck_chevalley' _ _ _ _ _ _ _ _ _ s (mono_of_pullback s is_lim) -- add is_lim entre s et (..)

-- Corollary 3.
variable (k)
lemma id_beck_chevalley : curried k ≫ (P C).map k.op = 𝟙 _ := 
begin
  have cond := curried_beck_chevalley (is_pullback_id_cone_of_monic k),
  simp only [pullback_cone.mk_fst, pullback_cone.mk_snd] at cond, 
  erw cond,
  dunfold P, simp only, erw pre_id, 
  rw [nat_trans.id_app, id_comp, curried_id], refl
end

end direct_image
