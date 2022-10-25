import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.reflexive
import category_theory.limits.opposites
import category_theory.closed.cartesian
import category_theory.adjunction.basic
import category_theory.functor.epi_mono
import category_theory.monad.basic
import category_theory.monad.monadicity
import category_theory.functor.basic

import topos

open category_theory category_theory.category category_theory.limits category_theory.cartesian_closed topos classifier opposite 

universes v u

noncomputable theory

variables (C : Type u) [category.{v} C] [topos C]


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

namespace preserves

variables {a b : Cᵒᵖ} {h k : a ⟶ b}

def fork_of_op_cofork (cof : cofork h k) : fork h.unop k.unop := 
fork.of_ι cof.π.unop (by { rw [←unop_comp, cof.condition, unop_comp] })

def op_cofork_of_fork (f : fork h.unop k.unop) : cofork h k :=
cofork.of_π f.ι.op 
begin
  change h with h.unop.op,
  rw [←op_comp, f.condition, op_comp], 
  refl,
end

lemma is_limit_fork_of_is_limit_op_cofork {cof : cofork h k} (coeq : is_colimit cof) :
  is_limit (fork_of_op_cofork cof) :=
begin
  apply fork.is_limit.of_exists_unique,
  intro s,
  let s_op := op_cofork_of_fork s,
  cases cofork.is_colimit.exists_unique coeq s_op.π s_op.condition with d hd,
  use d.unop,
  simp only at *,
  erw [fork.ι_of_ι, ←unop_comp, hd.left, cofork.π_of_π],
  split, refl,
  intro y, 
  change y with y.op.unop,
  rw ←unop_comp,
  intro hf,
  change s.ι with s_op.π.unop at hf,
  rw hd.right y.op (quiver.hom.unop_inj hf),
end

instance coreflexive_of_unop_reflexive {a b : Cᵒᵖ} (h k : a ⟶ b) [is_reflexive_pair h k] : 
  is_coreflexive_pair k.unop h.unop := 
{ common_retraction := ⟨(common_section h k).unop, 
    by { rw [←unop_id, ←unop_comp, ←unop_comp, section_comp_left, 
             section_comp_right, and_self] }⟩ }


lemma preserves_reflexive_coeq_aux {a b : Cᵒᵖ} {h k : a ⟶ b} [is_reflexive_pair h k] 
  (coeq : cofork h k) (is_colim : is_colimit coeq) : 
  is_colimit (cofork.of_π ((P C).map coeq.π) (by { rw [←category_theory.functor.map_comp, 
    coeq.condition, category_theory.functor.map_comp] }) : cofork ((P C).map h) ((P C).map k)) := 
begin
  let d := common_section h k,
  let g := fork_of_op_cofork coeq,
  have g_lim := is_limit_fork_of_is_limit_op_cofork is_colim,
  haveI : mono h.unop := 
  { right_cancellation := 
    begin 
      intros c u v heq,
      have sec := section_comp_left h k,
      rw [←comp_id u, ←unop_id, ←sec, unop_comp, ←assoc, heq, 
          assoc, ←unop_comp, sec, unop_id, comp_id],
    end },
  haveI : mono k.unop := 
  { right_cancellation := 
    begin 
      intros c u v heq,
      have sec := section_comp_right h k,
      rw [←comp_id u, ←unop_id, ←sec, unop_comp, ←assoc, heq, 
          assoc, ←unop_comp, sec, unop_id, comp_id],
    end },
  haveI : mono g.ι := 
  { right_cancellation := 
    begin 
      intros c u v heq,
      apply fork.is_limit.hom_ext g_lim heq
    end },
  haveI : is_coreflexive_pair k.unop h.unop := by apply_instance,
  have square := direct_image.curried_beck_chevalley 
    (is_pullback_of_equalizer_coreflexive_pair g_lim),
  simp only [pullback_cone.mk_fst, quiver.hom.op_unop, pullback_cone.mk_snd] at square,
  have g_id := direct_image.id_beck_chevalley g.ι,
  have h_id := direct_image.id_beck_chevalley h.unop,
  apply cofork.is_colimit.mk; intro s,
  swap 3, 
  { exact direct_image.curried g.ι ≫ s.π },
  { erw [←assoc, ←square, assoc, ←s.condition, ←assoc, h_id, id_comp] },
  { intros m hm, simp at hm,
    rw [←hm, ←assoc],
    erw [g_id, id_comp] }
end

variables {a b} {h k} [is_reflexive_pair h k] 

def colimit_desc {coeq : cocone (parallel_pair h k)} (is_colim : is_colimit coeq) 
  (s : cocone (parallel_pair h k ⋙ P C)) :=
(cofork.is_colimit.exists_unique (preserves_reflexive_coeq_aux coeq is_colim) (cofork.of_cocone s).π 
  (cofork.of_cocone s).condition)

variables (h k)

-- Is there a better way than to manually construct the whole colimit
-- and more directly use the coequalizer in the previous lemma
instance preserves_reflexive_coeq ⦃a b: Cᵒᵖ⦄ (h k : a ⟶ b) [is_reflexive_pair h k]  : 
  preserves_colimit (parallel_pair h k) (P C) := 
{ preserves := 
  begin
    intros coeq is_colim, 
    apply is_colimit.of_exists_unique, intro s,
    rcases colimit_desc is_colim s with ⟨w, ⟨hwl, hwr⟩⟩,
    simp only at hwr,
    use w, 
    split, 
    { simp only, rintro j, cases j; rw [←id_comp (s.ι.app _), ←eq_to_hom_refl _ (eq.refl _)],
      { erw ←cofork.of_cocone_ι s walking_parallel_pair.zero,
        rw ←(cofork.of_cocone s).w walking_parallel_pair_hom.left,
        change (cofork.of_cocone s).ι.app walking_parallel_pair.one with (cofork.of_cocone s).π,
        rw [←hwl,  ←assoc, ←((P C).map_cocone coeq).w walking_parallel_pair_hom.left], 
        refl },
      { erw ←cofork.of_cocone_ι s walking_parallel_pair.one,
        change (cofork.of_cocone s).ι.app walking_parallel_pair.one with (cofork.of_cocone s).π,
        rw ←hwl, refl }
    },
    intros l hl,
    apply hwr,
    erw hl walking_parallel_pair.one,
    change (cofork.of_cocone s).π with (cofork.of_cocone s).ι.app walking_parallel_pair.one,
    rw [cofork.of_cocone_ι s walking_parallel_pair.one, eq_to_hom_refl, id_comp],
  end }

end preserves

variable C

instance monadic_P : monadic_right_adjoint (P C) := 
@monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms 
  _ _ _ _ (P C) _ _ _ preserves.preserves_reflexive_coeq

namespace finite_colimits

variable C

def P_monad : monad C := (P_op_P_hom_equiv C).to_monad


def eilenberg_moore_has_finite_limits : has_finite_limits ((P_monad C).algebra) := 
{ out := λ J inst1 inst2,
  begin
  resetI,
  haveI : has_limits_of_shape J C := by apply_instance,
  haveI : has_limits_of_shape J (P_monad C).algebra := 
    has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape (P_monad C).forget,
  exactI has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape (P_monad C).forget,
  end }

instance : is_equivalence (monad.comparison (P_op_P_hom_equiv C)) := (monadic_P C).eqv

lemma C_op_equiv_eilenberg_moore : Cᵒᵖ ≌ (P_monad C).algebra := 
category_theory.functor.as_equivalence (monad.comparison (P_op_P_hom_equiv C))


instance has_finite_limits_C_op : has_finite_limits Cᵒᵖ :=
{ out := λ J inst1 inst2,
  begin
    resetI,
    haveI : has_limits_of_shape J (P_op_P_hom_equiv C).to_monad.algebra := 
      (eilenberg_moore_has_finite_limits C).out J,
    exact adjunction.has_limits_of_shape_of_equivalence (monad.comparison (P_op_P_hom_equiv C))
  end }

instance has_finite_colimits_C_opop : has_finite_colimits Cᵒᵖᵒᵖ := 
{ out := λ J _ _, by exactI has_colimits_of_shape_op_of_has_limits_of_shape }

lemma has_finite_colimits_C : has_finite_colimits C :=  
{ out := λ J _ _, by exactI adjunction.has_colimits_of_shape_of_equivalence 
  (op_op_equivalence C).inverse}

end finite_colimits

instance has_finite_colimits (C : Type u) [category.{v} C] [topos C] : has_finite_colimits C := 
finite_colimits.has_finite_colimits_C C