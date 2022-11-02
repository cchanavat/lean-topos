import category_theory.limits.shapes.binary_products
import category_theory.limits.opposites
import category_theory.closed.cartesian

import subobject_classifier
import adjunction
import image
import topos

open category_theory category_theory.category category_theory.limits 


/-!
Definitions and properties of direct image of a monic
Beck-Chevalley conditions

Only the first definition and the last theorems are not auxiliary junk
References : [MM92, IV.3] 
-/

universes v u

noncomputable theory

variables {C : Type u} [category.{v} C] [topos C]

open category_theory.limits.prod category_theory.cartesian_closed classifier opposite topos

namespace direct_image

variables {b b' c : C} (k : b' ⟶ b) [mono k]

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

-- We follow [MM92, IV.3.2], with mostly their notations
variables (s : pullback_cone g k) 

def upper_right_rectangle (k : b' ⟶ b) [mono k] : pullback_cone (uncurried k) (truth C) :=
pullback_cone.mk (canonical_incl (in_map b') ≫ map k (𝟙 _)) (terminal.from _) (classifier.comm _)

def upper_left_bottom : pullback_cone (map g (𝟙 ((P C).obj (op b')))) (map k (𝟙 ((P C).obj (op b')))) :=
pullback_cone.mk (map s.fst (𝟙 _)) (map s.snd (𝟙 _)) (by { rw [map_map, map_map, s.condition] })

def lower_right_rectangle [mono s.fst] : pullback_cone (uncurried s.fst) (truth C) := 
pullback_cone.mk (canonical_incl (in_map s.X) ≫ map s.fst (𝟙 _)) (terminal.from _) (classifier.comm _)

def lower_left_bottom : pullback_cone (map (𝟙 _) ((P C).map s.snd.op)) (map s.fst (𝟙 _))  :=
pullback_cone.mk (map s.fst (𝟙 _))  (map (𝟙 _) ((P C).map s.snd.op))
(by repeat { rw [map_map, id_comp, comp_id] }) 

lemma is_pullback_upper_right_rectangle : is_limit (upper_right_rectangle k) :=
classifier.is_pb _

lemma is_pullback_upper_left_bottom (is_lim : is_limit s) : is_limit (upper_left_bottom s) :=
is_pullback_of_prod_pullback is_lim (is_pullback_square_ids_snd _)

lemma is_pullback_lower_right_rectangle [mono s.fst] : is_limit (lower_right_rectangle s) :=
classifier.is_pb _

lemma is_pullback_lower_left_bottom (is_lim : is_limit s) : is_limit (lower_left_bottom s) :=
is_pullback_of_prod_pullback (is_pullback_square_ids_fst _) (is_pullback_square_ids_snd _)

def upper_big_canonical := canonical_incl (map s.snd (𝟙 _) ≫ in_map b')

namespace upper

def left : pullback (map s.snd (𝟙 _)) (canonical_incl (in_map b')) ⟶ s.X ⨯ (P C).obj (op b') := 
pullback.fst

def top : pullback (map s.snd (𝟙 _)) (canonical_incl (in_map b')) ⟶ s{in_map b'}s := 
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

end upper

namespace lower

def left : 
  pullback (map (𝟙 s.X) ((P C).map s.snd.op)) (canonical_incl (in_map s.X)) ⟶ _ := 
pullback.fst

def top : 
  pullback (map (𝟙 s.X) ((P C).map s.snd.op)) (canonical_incl (in_map s.X)) ⟶ s{in_map s.X}s := 
pullback.snd 

def cone : pullback_cone (map (𝟙 s.X) ((P C).map s.snd.op) ≫ in_map s.X) (truth C) :=
pullback_cone.mk (left s) (top s ≫ terminal.from _)
begin
  erw [←assoc, pullback.condition], 
  rw [assoc, canonical_incl_comm, assoc], 
  refl,
end

lemma is_pullback_cone: is_limit (cone s) :=
big_square_is_pullback (top s) (terminal.from _)
    (map (𝟙 s.X) ((P C).map s.snd.op)) (in_map s.X) (left s) (canonical_incl (in_map s.X)) (truth C)
    pullback.condition (canonical_incl_comm (in_map s.X)) 
    (canonical_is_pullback _) (pullback_is_pullback _ _)

end lower

namespace lower_big

def left_rectangle_flipped : 
  pullback_cone (canonical_incl (in_map s.X) ≫ map s.fst (𝟙 _)) (map (𝟙 c) ((P C).map s.snd.op)) :=
pullback_cone.mk (lower.top s) (lower.left s ≫ map s.fst (𝟙 _))
begin
  rw assoc,
  erw (lower_left_bottom s).condition,
  rw ←assoc,
  erw ←pullback.condition,
  rw assoc, refl,
end

lemma is_pullback_left_rectangle_flipped (s_lim : is_limit s) : 
  is_limit (left_rectangle_flipped s) :=
big_square_is_pullback (lower.left s) (map s.fst (𝟙 _))
    (canonical_incl (in_map s.X)) (map s.fst (𝟙 _)) (lower.top s)
    (map (𝟙 s.X) ((P C).map s.snd.op)) (map (𝟙 c) ((P C).map s.snd.op))
    pullback.condition.symm (lower_left_bottom s).condition.symm 
    (pullback_cone.flip_is_limit (is_pullback_lower_left_bottom s s_lim))
    (pullback_cone.flip_is_limit (pullback_is_pullback _ _))

def left_rectangle : 
  pullback_cone (map (𝟙 c) ((P C).map s.snd.op)) (canonical_incl (in_map s.X) ≫ map s.fst (𝟙 _)) :=
pullback_cone.mk (lower.left s ≫ map s.fst (𝟙 _)) (lower.top s) 
(left_rectangle_flipped _).condition.symm

lemma is_pullback_left_rectangle (s_lim : is_limit s) : is_limit (left_rectangle s) :=
pullback_cone.flip_is_limit (is_pullback_left_rectangle_flipped s s_lim)

def big_square [mono s.fst] : pullback_cone (map (𝟙 c) ((P C).map s.snd.op) ≫ uncurried s.fst) (truth C) :=
pullback_cone.mk (lower.left s ≫ map s.fst (𝟙 _)) (lower.top s ≫ terminal.from _)
begin
  nth_rewrite 1 assoc,
  erw ←(lower_right_rectangle s).condition,
  rw [←assoc, ←assoc], 
  apply eq_whisker,
  rw assoc, erw ←(left_rectangle s).condition,
  rw ←assoc, refl,
end

lemma is_pullback_big_square (s_lim : is_limit s) [mono s.fst] : is_limit (big_square s) :=
big_square_is_pullback (lower.top s) (terminal.from _)
  (map (𝟙 c) ((P C).map s.snd.op)) (uncurried s.fst)
  (lower.left s ≫ map s.fst (𝟙 _)) (canonical_incl (in_map s.X) ≫ map s.fst (𝟙 _))
  (truth C) (left_rectangle s).condition (lower_right_rectangle s).condition 
  (is_pullback_lower_right_rectangle s)
  (is_pullback_left_rectangle s s_lim)

end lower_big

namespace upper_big

def left_rectangle_flipped : 
  pullback_cone (canonical_incl (in_map b') ≫ map k (𝟙 _)) (map g (𝟙 _)) :=
pullback_cone.mk (upper.top s) (upper.left s ≫ map s.fst (𝟙 _))
begin
  rw assoc,
  erw (upper_left_bottom s).condition,
  rw ←assoc,
  erw ←pullback.condition,
  rw assoc, refl,
end

lemma is_pullback_left_rectangle_flipped (s_lim : is_limit s) : 
  is_limit (left_rectangle_flipped s) :=
big_square_is_pullback (upper.left s) (map s.fst (𝟙 _))
    (canonical_incl (in_map b')) (map k (𝟙 _)) (upper.top s)
    (map s.snd (𝟙 _)) (map g (𝟙 _))
    pullback.condition.symm (upper_left_bottom s).condition.symm 
    (pullback_cone.flip_is_limit (is_pullback_upper_left_bottom s s_lim))
    (pullback_cone.flip_is_limit (pullback_is_pullback _ _))

def left_rectangle : 
  pullback_cone (map g (𝟙 _)) (canonical_incl (in_map b') ≫ map k (𝟙 _)) :=
pullback_cone.mk (upper.left s ≫ map s.fst (𝟙 _)) (upper.top s) 
(left_rectangle_flipped _).condition.symm

lemma is_pullback_left_rectangle (s_lim : is_limit s) : is_limit (left_rectangle s) :=
pullback_cone.flip_is_limit (is_pullback_left_rectangle_flipped s s_lim)

def big_square [mono s.fst] : pullback_cone (map g (𝟙 _) ≫ uncurried k) (truth C) :=
pullback_cone.mk (upper.left s ≫ map s.fst (𝟙 _)) (upper.top s ≫ terminal.from _)
begin
  nth_rewrite 1 assoc,
  erw ←(upper_right_rectangle k).condition,
  rw [←assoc, ←assoc], 
  apply eq_whisker,
  rw assoc, erw ←(left_rectangle s).condition,
  rw ←assoc, refl,
end

lemma is_pullback_big_square (s_lim : is_limit s) [mono s.fst] : is_limit (big_square s) :=
big_square_is_pullback (upper.top s) (terminal.from _)
  (map g (𝟙 _)) (uncurried k)
  (upper.left s ≫ map s.fst (𝟙 _)) (canonical_incl (in_map b') ≫ map k (𝟙 _))
  (truth C) (left_rectangle s).condition (upper_right_rectangle k).condition 
  is_pullback_upper_right_rectangle
  (is_pullback_left_rectangle s s_lim)

end upper_big

namespace lower_upper

variables {s} 

def low_of_up (t : pullback_cone (map s.snd (𝟙 _) ≫ in_map b') (truth C)) : 
  pullback_cone (map (𝟙 s.X) ((P C).map s.snd.op) ≫ in_map s.X) (truth C) :=
pullback_cone.mk t.fst (terminal.from _) 
begin
  erw [←in_map_dinatural, t.condition], 
  congr,
end

def up_of_low (t : pullback_cone (map (𝟙 s.X) ((P C).map s.snd.op) ≫ in_map s.X) (truth C)) : 
  pullback_cone (map s.snd (𝟙 _) ≫ in_map b') (truth C) :=
pullback_cone.mk t.fst (terminal.from _) 
begin
  rw [in_map_dinatural, t.condition], 
  congr,
end

variable (s) 

def cone : pullback_cone (map (𝟙 s.X) ((P C).map s.snd.op) ≫ in_map s.X) (truth C) :=
low_of_up (upper.cone s)

def lift_cone (t : pullback_cone (map (𝟙 s.X) ((P C).map s.snd.op) ≫ in_map s.X) (truth C)) := 
pullback_cone.is_limit.lift' (upper.is_pullback_cone s) (up_of_low t).fst (up_of_low t).snd (up_of_low t).condition

lemma is_pullback_cone : is_limit (cone s) :=
begin
  apply pullback_cone.is_limit.mk _ (λ t, (lift_cone s t).val); intro t; simp only,
  { exact (lift_cone s t).prop.left },
  { apply is_terminal.hom_ext terminal_is_terminal },
  { intros r hfst hsnd,
    apply pullback_cone.is_limit.hom_ext (upper.is_pullback_cone s),
      erw [hfst, (lift_cone s t).prop.left], refl,
      apply is_terminal.hom_ext terminal_is_terminal }
end
end lower_upper

-- 

instance (s_lim : is_limit s) : mono (s.fst) := pullback_cone.mono_fst_of_is_pullback_of_mono s_lim

def iso_X := is_limit.cone_point_unique_up_to_iso (lower_upper.is_pullback_cone s) (lower.is_pullback_cone s)

lemma iso_comm_X_hom : 
  (iso_X s).hom ≫ lower.left s ≫ map s.fst (𝟙 _) = upper.left s ≫ map s.fst (𝟙 _) :=
begin
  rw ←assoc,
  apply eq_whisker,
  apply is_limit.cone_point_unique_up_to_iso_hom_comp 
    (lower_upper.is_pullback_cone s) (lower.is_pullback_cone s) walking_cospan.left
end

lemma iso_comm_X_inv : 
  (iso_X s).inv ≫ upper.left s ≫ map s.fst (𝟙 _) = lower.left s ≫ map s.fst (𝟙 _) :=
by { rw [←iso_comm_X_hom, ←assoc, iso.inv_hom_id, id_comp] }

lemma mono_lower_left (s_lim : is_limit s) : mono (lower.left s ≫ map s.fst (𝟙 _)) :=
begin
  haveI := pullback_cone.mono_fst_of_is_pullback_of_mono s_lim,
  apply pullback_cone.mono_fst_of_is_pullback_of_mono (lower_big.is_pullback_big_square s s_lim),
end

lemma mono_upper_left (s_lim : is_limit s) : mono (upper.left s ≫ map s.fst (𝟙 _)) := 
begin
  rw ←iso_comm_X_hom,
  haveI := mono_lower_left s s_lim,
  apply mono_comp
end


abbreviation upleft := upper.left s ≫ map s.fst (𝟙 _)
abbreviation lowleft := lower.left s ≫ map s.fst (𝟙 _)

variable {s}

lemma mono_lowleft (s_lim : is_limit s) : mono (lowleft s) := mono_lower_left s s_lim
lemma mono_upleft (s_lim : is_limit s) : mono (upleft s) := mono_upper_left s s_lim

lemma classifier_upleft_eq_upper_bot [mono s.fst] (s_lim : is_limit s) :
  @classifier_of _ _ _ _ _ _ (upleft s) (mono_upleft s_lim) = 
   map g (𝟙 _) ≫ uncurried k :=
begin
  apply uniquely,
  refine {comm := _, is_pb := _},
  convert (upper_big.big_square s).condition,
  convert (upper_big.is_pullback_big_square s s_lim),
  apply is_terminal.hom_ext terminal_is_terminal
end


def upper_left_big_lift [mono s.fst] (s_lim : is_limit s)
  (t : pullback_cone (map (𝟙 c) ((P C).map s.snd.op) ≫ uncurried s.fst) (truth C)) :=
pullback_cone.is_limit.lift' (lower_big.is_pullback_big_square s s_lim) t.fst t.snd t.condition

lemma classifier_upleft_eq_lower_bot [mono s.fst] (s_lim : is_limit s) :
  @classifier_of _ _ _ _ _ _ (upleft s) (mono_upleft s_lim) = 
  map (𝟙 _) ((P C).map s.snd.op) ≫ uncurried s.fst :=
begin
  apply uniquely,
  refine {comm := _, is_pb := _},
  dunfold upleft,
  erw ←iso_comm_X_hom,  
  rw assoc,
  erw (lower_big.big_square s).condition,
  symmetry,
  rw [←iso.inv_comp_eq, ←assoc, terminal.comp_from], congr,

  apply pullback_cone.is_limit.mk _ (λ t, (upper_left_big_lift s_lim t).val ≫ (iso_X s).inv);
  intro t; simp only,
  { rw [assoc, iso_comm_X_inv], 
    erw (upper_left_big_lift s_lim t).prop.left },
  { apply is_terminal.hom_ext terminal_is_terminal },
  { intros r hfst hsdn, rw iso.eq_comp_inv,
    apply pullback_cone.is_limit.hom_ext (lower_big.is_pullback_big_square s s_lim),
      erw (upper_left_big_lift s_lim t).prop.left,
      rw assoc, erw [iso_comm_X_hom, hfst],
      apply is_terminal.hom_ext terminal_is_terminal }
end


lemma uncurried_beck_chevalley [mono s.fst] (s_lim : is_limit s) :
  map g (𝟙 _) ≫ uncurried k = map (𝟙 _) ((P C).map s.snd.op) ≫ uncurried s.fst := 
by rw [←classifier_upleft_eq_lower_bot, ←classifier_upleft_eq_upper_bot s_lim]


lemma curried_beck_chevalley' [mono s.fst] (s_lim : is_limit s) :
  curried k ≫ (P C).map g.op = (P C).map s.snd.op ≫ curried s.fst := 
begin
  dunfold curried,
  have eq := congr_arg curry (uncurried_beck_chevalley s_lim) ,
  rw curry_natural_left at eq,
  erw [←eq, eq_curry_iff, uncurry_natural_left, uncurry_pre],
  clear eq,
  erw [←assoc, map_map, id_comp, comp_id (curry (uncurried k))],
  rw [←comp_id g.op.unop, ←id_comp (curry (uncurried k)), ←map_map, assoc],
  rw [←uncurry_eq, uncurry_curry], refl,
end


variable {s}
def curried_beck_chevalley (is_lim : is_limit s) :=
  @curried_beck_chevalley' _ _ _ _ _ _ _ _ _ s (mono_of_pullback s is_lim) is_lim

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