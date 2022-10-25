import category_theory.limits.shapes
import category_theory.limits.preserves.limits
import category_theory.limits.shapes.reflexive

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

-- The product of two pullback square is a pullback square,
-- already in mathlib in a more abstract way (i.e. limits commutes)
-- but redoing it here is probably easier

open category_theory.limits.prod

variables {U V W Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} 
  {s : pullback_cone f g} {h : U ⟶ W} {k : V ⟶ W} 
  {t : pullback_cone h k} 

def map_lift (s_lim : is_limit s) (t_lim : is_limit t) (u : pullback_cone (map f h) (map g k)) :
  {l // l ≫ s.fst = u.fst ≫ fst ∧ l ≫ s.snd = u.snd ≫ fst} 
× {l // l ≫ t.fst = u.fst ≫ snd ∧ l ≫ t.snd = u.snd ≫ snd} :=
begin
  let u_fst := eq_whisker u.condition fst,
  let u_snd := eq_whisker u.condition snd,
  rw [assoc, assoc] at u_fst u_snd,
  rw [map_fst, map_fst, ←assoc, ←assoc] at u_fst,
  rw [map_snd, map_snd, ←assoc, ←assoc] at u_snd,
  exact (pullback_cone.is_limit.lift' s_lim (u.fst ≫ fst) (u.snd ≫ fst) u_fst, 
         pullback_cone.is_limit.lift' t_lim (u.fst ≫ snd) (u.snd ≫ snd) u_snd)
end

lemma is_pullback_of_prod_pullback (s_lim : is_limit s) (t_lim : is_limit t) :
  is_limit (pullback_cone.mk (map s.fst t.fst) (map s.snd t.snd) 
           (by { rw [map_map, s.condition, t.condition, ←map_map] })) := 
begin
  apply pullback_cone.is_limit.mk _ 
    (λ u, lift (map_lift s_lim t_lim u).1.val (map_lift s_lim t_lim u).2.val); 
  simp only; intro u,
  { rw lift_map, 
    erw [(map_lift s_lim t_lim u).1.prop.left, (map_lift s_lim t_lim u).2.prop.left],
    rw [←comp_lift, lift_fst_snd, comp_id] },
  { rw lift_map, 
    erw [(map_lift s_lim t_lim u).1.prop.right, (map_lift s_lim t_lim u).2.prop.right],
    rw [←comp_lift, lift_fst_snd, comp_id] },
  { intros l' hfst hsnd,
    apply hom_ext, 
    { apply pullback_cone.is_limit.hom_ext s_lim, 
        rw [lift_fst, assoc, ←map_fst s.fst t.fst, ←assoc, hfst], 
        erw [(map_lift s_lim t_lim u).1.prop.left],
        
        rw [lift_fst, assoc, ←map_fst s.snd t.snd, ←assoc, hsnd], 
        erw [(map_lift s_lim t_lim u).1.prop.right] },
    { apply pullback_cone.is_limit.hom_ext t_lim, 
        rw [lift_snd, assoc, ←map_snd s.fst t.fst, ←assoc, hfst], 
        erw [(map_lift s_lim t_lim u).2.prop.left],
        
        rw [lift_snd, assoc, ←map_snd s.snd t.snd, ←assoc, hsnd], 
        erw [(map_lift s_lim t_lim u).2.prop.right] } }
end

lemma is_pullback_square_ids_fst{c d : C} (f : c ⟶ d) : 
  is_limit (pullback_cone.mk f (𝟙 c) (by simp) : pullback_cone (𝟙 d) f) :=
begin
  apply pullback_cone.is_limit.mk _ (λ s, s.snd); simp only,
  exact (λ s, by { rw [←s.condition, comp_id] }),
  exact (λ s, by rw comp_id s.snd),
  exact (λ s t h1 h2, by { rw [←h2, comp_id] })
end

lemma is_pullback_square_ids_snd {c d : C} (f : c ⟶ d) : 
  is_limit (pullback_cone.mk (𝟙 c) f (by simp) : pullback_cone f (𝟙 d)) :=
begin
  apply pullback_cone.is_limit.mk _ (λ s, s.fst); simp only,
  exact (λ s, by rw comp_id s.fst),
  exact (λ s, by { rw [s.condition, comp_id] }),
  exact (λ s t h1 h2, by { rw [←h1, comp_id] })
end


def lift_pullback_of_equalizer_coreflexive_pair {c d : C} {h k : c ⟶ d} {u : fork k h} 
  [is_coreflexive_pair h k] (u_lim : is_limit u) (s : pullback_cone h k) : 
  {l // l ≫ u.ι = s.fst ∧ l ≫ u.ι = s.snd} := 
begin
  have cond := eq_whisker s.condition (common_retraction h k),
  rw [assoc, assoc, right_comp_retraction, left_comp_retraction, comp_id, comp_id] at cond,
  rw ←cond, simp only [and_self],
  refine fork.is_limit.lift' u_lim s.fst _,
  nth_rewrite 0 cond,
  exact s.condition.symm
end

def is_pullback_of_equalizer_coreflexive_pair {c d : C} {h k : c ⟶ d} {u : fork k h} 
  (u_lim : is_limit u) [is_coreflexive_pair h k] : 
  is_limit (pullback_cone.mk u.ι u.ι (by rw u.condition) : pullback_cone h k) :=
begin
  apply pullback_cone.is_limit.mk _ 
  (λ s, (lift_pullback_of_equalizer_coreflexive_pair u_lim s).val); 
  intro s; simp only,
    exact (lift_pullback_of_equalizer_coreflexive_pair u_lim s).prop.left,
    exact (lift_pullback_of_equalizer_coreflexive_pair u_lim s).prop.right,
    intros m hfst hsnd, apply fork.is_limit.hom_ext u_lim,
    erw [hfst, (lift_pullback_of_equalizer_coreflexive_pair u_lim s).prop.left]
end

lemma is_pullback_id_cone_of_monic {c d : C} (k : c ⟶ d) [mono k] :
  is_limit (pullback_cone.mk (𝟙 c) (𝟙 c) (by rw id_comp) : pullback_cone k k) :=
begin
  apply pullback_cone.is_limit.mk _ (λ s, s.fst); intro s; simp only,
  { rw comp_id },
  { rw [comp_id, ←cancel_mono k, s.condition] },
  { intros u hf hs, rw ←hf, rw comp_id }
end