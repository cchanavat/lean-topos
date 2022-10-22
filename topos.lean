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

open category_theory category_theory.category category_theory.limits classifier


/-!
# Topos

Basic definitions of a topos

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

variables {C} (X : C)

def sub_to_hom : subobject X → (X ⟶ Ω C) := λ s, classifier_of s.arrow
def hom_to_sub : (X ⟶ Ω C) → subobject X := λ σ, canonical_sub σ

lemma sub_equiv_hom : subobject X ≃ (X ⟶ Ω C) := 
{ to_fun := sub_to_hom X,
  inv_fun := hom_to_sub X,
  left_inv := λ S, sub_eq_canonical_sub_of_classifier S,  
  right_inv := λ σ, classifier.uniquely _ _ 
                   (classifying_pullback.mk _ (is_pullback_canonical_arrow _)) }



open opposite category_theory.cartesian_closed

def δ := classifier_of (diag X)
def singleton_map := curry (δ X)

namespace delta 

variables {C X} {Y : C} {f : X ⟶ Y}

open category_theory.limits.prod

def pullback_cone_map_diag (f : X ⟶ Y) : pullback_cone (map f (𝟙 _)) (diag Y) :=
pullback_cone.mk (lift (𝟙 _) f) f (by simp only [lift_map,comp_lift, id_comp, comp_id])

lemma cone_map_diag_fst (s : pullback_cone (map f (𝟙 _)) (diag Y)) : s.fst ≫ fst ≫ f = s.snd :=
by { rw [←map_fst f (𝟙 _), ←assoc, s.condition, assoc, lift_fst, comp_id] }

lemma cone_map_diag_snd (s : pullback_cone (map f (𝟙 _)) (diag Y)) : s.fst ≫ snd = s.snd :=
by { rw [←comp_id (s.fst ≫ snd), assoc, ←map_snd f (𝟙 _), 
         ←assoc, s.condition, assoc, lift_snd, comp_id] }

lemma cone_map_diag_fst_snd (s : pullback_cone (map f (𝟙 _)) (diag Y)) : 
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

def big_square_cone : pullback_cone (map f (𝟙 Y) ≫ δ Y) (truth C) :=
pullback_cone.mk (lift (𝟙 X) f) (f ≫ terminal.from Y) 
(by { erw [←assoc, (pullback_cone_map_diag f).condition, assoc, classifier.comm (diag Y),
      ←assoc, terminal.comp_from] })

lemma is_limit_big_square_cone : is_limit (big_square_cone f) :=
begin
  apply big_square_is_pullback f (terminal.from _) (map f (𝟙 _)) (δ _) 
    (lift (𝟙 _) f) (diag _) (truth C),
  apply classifier.is_pb,
  apply is_limit_pullback_cone_map_diag,
end

lemma big_square_classifying : classifying (truth C) (lift (𝟙 X) f) (map f (𝟙 Y) ≫ δ Y) := 
{ comm := by { rw ←terminal.comp_from f, erw (big_square_cone f).condition, refl },
  is_pb := 
  begin
    let g := is_limit_big_square_cone f, unfold big_square_cone at g,
    simp [terminal.comp_from f] at g, assumption,
  end }

lemma classifies : classifier_of (lift (𝟙 _) f) = map f (𝟙 _) ≫ δ Y :=
classifier.uniquely _ _ (big_square_classifying f)

variable (g : X ⟶ Y)

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

variables {C} {X} {Y : C}

lemma iso_of_is_limit_fork_id {f : X ⟶ Y} {s : fork f f} (is_lim : is_limit s) : is_iso s.ι :=
begin
  apply is_iso.mk,
  use is_lim.lift (fork.of_ι (𝟙 X) (by simp)),
  split,
  { apply fork.is_limit.hom_ext is_lim,
    rw [assoc, fork.is_limit.lift_ι, fork.ι_of_ι, id_comp],
    apply comp_id },
  { apply fork.is_limit.lift_ι }
end

lemma is_limit_of_is_limit_fork_eq {f g : X ⟶ Y} {s : fork f g} (is_lim : is_limit s) (heq : f = g) : 
  is_limit (fork.of_ι s.ι (by rw s.condition) : fork f f) :=
begin
  refine fork.is_limit.mk _ 
    (λ t : fork f f, (fork.is_limit.lift' is_lim t.ι (by rw ←heq)).val) _ _; 
  intro t,
  { apply fork.is_limit.lift_ι },
  { intros r ht, apply fork.is_limit.hom_ext is_lim, erw fork.is_limit.lift_ι, apply ht }
end

lemma iso_of_is_limit_fork_eq {f g : X ⟶ Y} {s : fork f g} (is_lim : is_limit s) (heq : f = g) : 
  is_iso s.ι := iso_of_is_limit_fork_id (is_limit_of_is_limit_fork_eq is_lim heq)

variable (C)

instance topos_balanced : balanced C :=
{ is_iso_of_mono_of_epi := λ X Y f m e,
  begin
    resetI,
    apply iso_of_is_limit_fork_eq (image.monic_is_limit_fork f),
    rw ←cancel_epi f,
    exact (image.monic_to_canonical_fork f).condition
  end }

def P : Cᵒᵖ ⥤ C := {
  obj := λ c, (exp c.unop).obj (Ω C),
  map := λ c d f, (pre f.unop).app (Ω C),
  map_id' := λ c, by {rw [unop_id, pre_id, nat_trans.id_app]},
  map_comp' := λ _ _ _ f g, by {rw [unop_comp, pre_map, nat_trans.comp_app]} }

def P_op : C ⥤ Cᵒᵖ := functor.right_op (P C) 



-- We follow McLane and describe the chain of natural iso to prove
-- P_op ⊣ P of Theorem IV.5.1
-- There should definitely be a clever way

def prod_yoneda_Ω : (Cᵒᵖ × Cᵒᵖ) ⥤ Type v := 
{ obj := λ x, (yoneda.obj (Ω C)).obj (op (x.1.unop ⨯ x.2.unop)), 
  map := λ x y f, (yoneda.obj (Ω C)).map (limits.prod.map f.1.unop f.2.unop).op,
  map_id' := λ x, by simp,
  map_comp' := λ x y z f g, 
  begin 
    rw ←functor.map_comp, congr, 
    rw [←op_comp, limits.prod.map_map, ←unop_comp, ←unop_comp],
    congr
   end }

def prod_yoneda_iso_right_hom : prod_yoneda_Ω C ≅ right_hom (P C) :=
{ hom := 
  { app := λ x f, curry ((prod.braiding x.1.unop x.2.unop).inv ≫ f),
    naturality' := λ x y f, 
    begin 
      ext g, repeat {rw [types_comp_apply, prod.braiding_inv]},
      rw curry_eq_iff,
      dunfold right_hom P, simp only,
      rw [←assoc, uncurry_natural_left, uncurry_pre, ←assoc, limits.prod.map_map, id_comp, comp_id,
          ←comp_id f.snd.unop, ←limits.prod.map_map, assoc, ←uncurry_eq, uncurry_curry],
      dunfold prod_yoneda_Ω yoneda, simp only, rw quiver.hom.unop_op,
      erw [←assoc, ←assoc, braid_natural, ←braid_natural]
     end },
  inv := 
  { app := λ x f, (prod.braiding x.1.unop x.2.unop).hom ≫ uncurry f,
    naturality' := λ x y f,
    begin
      ext g, repeat {rw [types_comp_apply, prod.braiding_hom]},
      dunfold right_hom P, simp only,
      rw [←assoc, uncurry_natural_left, uncurry_pre],
      nth_rewrite 1 ←assoc, 
      rw [limits.prod.map_map, id_comp, comp_id, ←comp_id f.snd.unop,
          ←limits.prod.map_map, assoc, ←uncurry_eq, ←assoc],
      erw ←braid_natural, 
      dunfold prod_yoneda_Ω yoneda, simp only,
      rw [prod.braiding_hom, assoc, quiver.hom.unop_op],
    end },
  hom_inv_id' := 
  begin 
    ext x f, 
    simp only [prod.braiding_inv, uncurry_curry, prod.braiding_hom, 
               functor_to_types.comp, nat_trans.id_app, types_id_apply], 
    rw [←assoc, prod.symmetry'], apply id_comp,
  end,
  inv_hom_id' := 
  begin
    ext x f, 
    simp only [prod.braiding_inv, prod.braiding_hom, functor_to_types.comp, 
               nat_trans.id_app, types_id_apply], 
    erw [←assoc, prod.symmetry', id_comp (uncurry f), curry_uncurry]
  end }

def left_hom_iso_prod_yoneda : left_hom (P_op C) ≅ prod_yoneda_Ω C :=
{ hom := 
  { app := λ x f, uncurry f.unop,
    naturality' := λ x y f, 
    begin 
      ext g, simp, dunfold left_hom prod_yoneda_Ω P_op P, 
      simp only [functor.right_op_map, quiver.hom.op_unop, unop_comp, 
                 quiver.hom.unop_op, assoc, yoneda_obj_map],
      erw [←assoc, uncurry_natural_left, uncurry_pre, ←assoc ,uncurry_eq, limits.prod.map_map, 
           id_comp, comp_id, ←assoc, limits.prod.map_map], 
      congr, rw comp_id,
    end}, 
  inv := 
  { app := λ x f, (curry f).op,
    naturality' := λ x y f,
    begin 
      ext g, dunfold left_hom prod_yoneda_Ω P_op P, 
      simp only [types_comp_apply, yoneda_obj_map, quiver.hom.unop_op, 
                 functor.right_op_map],
      nth_rewrite 1 ←quiver.hom.op_unop f.snd,
      rw [←op_comp, ←op_comp],
      congr,
      rw [curry_eq_iff, uncurry_natural_left, uncurry_pre, ←assoc, 
          limits.prod.map_map, id_comp,  ←comp_id f.fst.unop], 
      nth_rewrite 2 comp_id,
      rw [←limits.prod.map_map, assoc],
      change op (unop x.fst) with x.fst,
      rw [←uncurry_eq (curry g), comp_id, uncurry_curry],
    end },
  hom_inv_id' := by { ext, simp },
  inv_hom_id' := by { ext, simp },}

def P_op_P_hom_equiv : P_op C ⊣ P C := 
adjunction_of_left_hom_iso_right (left_hom_iso_prod_yoneda C ≪≫ prod_yoneda_iso_right_hom C)

instance : is_right_adjoint (P C) := is_right_adjoint.mk _ (P_op_P_hom_equiv C)

-- Now we will follow IV.5.3 to prove that P is monadic
-- As a corollary, we have all finite colimits
variable {C}
lemma uncurry_singleton_P_map_simp {d c : C} (f : d ⟶ c) : 
  uncurry (singleton_map c ≫ (P C).map f.op) = limits.prod.map f (𝟙 _) ≫ δ c :=
begin
  dunfold P, simp,
  rw [uncurry_natural_left,uncurry_pre, ←assoc, limits.prod.map_map],
  change (unop (op c)) with c,
  rw [id_comp, comp_id, ←id_comp (singleton_map c), ←comp_id f, 
      ←limits.prod.map_map, assoc],
  erw [←uncurry_eq, uncurry_curry, comp_id],
end

instance P_faithful : faithful (P C) := 
{ map_injective' :=
  begin
    intros c d h k heq,
    have eq := congr_arg uncurry (whisker_eq (singleton_map c.unop) heq),
    rw [←quiver.hom.op_unop h, ←quiver.hom.op_unop k,
        uncurry_singleton_P_map_simp h.unop,  uncurry_singleton_P_map_simp k.unop,
        ←delta.classifies, ←delta.classifies, delta.cancel_classifier] at eq,
    apply quiver.hom.unop_inj eq
  end }

instance P_reflects_iso : reflects_isomorphisms (P C) := 
begin
  haveI : balanced Cᵒᵖ := balanced_opposite,
  apply_instance,
end


instance preserves_reflexive_coeq (c d : Cᵒᵖ) (f g : c ⟶ d) [inst : is_reflexive_pair f g] : 
  preserves_colimit (parallel_pair f g) (P C) := 
begin
  sorry
end

def monadic_P : monadic_right_adjoint (P C) := 
@monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms 
  _ _ _ _ (P C) _ _ _ preserves_reflexive_coeq
