import tactic.congrm
import category_theory.limits.shapes.finite_limits
import category_theory.closed.cartesian
import category_theory.closed.types
import category_theory.limits.shapes.functor_category
import category_theory.limits.functor_category
import category_theory.limits.types
import category_theory.functor
import category_theory.sites.sieves

import topos
import subobject_classifier
import pullbacks
import image

open category_theory category_theory.category category_theory.limits classifier functor

universes v u

noncomputable theory


variables {C : Type u} [category.{u} C] [small_category C]

local notation `°`:std.prec.max_plus C := Cᵒᵖ ⥤ Type u
local notation `₸` := ⊤_ (°C)

namespace presheaf

/-
  Ω in a presheaf topos is defined to be
  Ω_c = all the sieves on c
-/


def sieve_map (c d : C) (f : c ⟶ d) : sieve d ⟶ sieve c := sieve.pullback f

abbreviation Ω_obj (c : Cᵒᵖ) := (sieve c.unop)
abbreviation Ω_map (c d : Cᵒᵖ) (f : c ⟶ d) : (Ω_obj c ⟶ Ω_obj d ):= sieve_map _ _ f.unop

def Ω : °C := {
  obj := Ω_obj,
  map := Ω_map,
  map_id' := 
  begin
    intro, dunfold Ω_map sieve_map,
    funext, simp 
  end,
  map_comp' := 
  begin
    intros X Y Z f g, dunfold Ω_map sieve_map, 
    funext, simp [sieve.pullback_comp]
  end,
}

@[simp] lemma obj' (c : Cᵒᵖ) : (Ω.obj c) = (Ω_obj c) := by refl
instance (c : Cᵒᵖ) : complete_lattice (Ω.obj c) := by simp; apply_instance

 
def truth : ₸ ⟶ Ω := { app := λ c x, ⊤ }

@[simp] lemma truth_app (c : Cᵒᵖ) (x : ₸.obj c) : truth.app c x = ⊤ := by refl

-- Some basics types in Type u to work with --
def uUnit : Type u := ulift unit
def uStar : uUnit := ulift.up unit.star

def uBool : Type u := ulift bool
def fuBool (x y : ⊤_ (Type u)) (b : uBool) : ⊤_ (Type u) :=
match b.down with
| tt := x
| ff := y
end

namespace terminal
/- Let us prove that the terminimport tactic.simp_rwal object in Type u is iso the one element type -/

lemma type_uniq (b a : ⊤_ (Type u)) : a = b := 
begin
  have h : (fuBool a b : uBool ⟶ ⊤_ (Type u)) = (fuBool b a : uBool ⟶ ⊤_ (Type u)) := by 
    rw [←is_terminal.hom_ext terminal_is_terminal (terminal.from uBool) (fuBool b a), 
        ←is_terminal.hom_ext terminal_is_terminal (terminal.from uBool) (fuBool a b)],
  exact congr_fun h (ulift.up tt),
end

instance type_unique : unique (⊤_ (Type u)) :=
{ default := (terminal.from uUnit : uUnit → (⊤_ (Type u))) uStar,
  uniq := type_uniq _ }

/- Explicit construction of a terminal presheaf, named T -/
def T : °C := (category_theory.functor.const (Cᵒᵖ)).obj (⊤_ (Type u))

lemma T_proj (c : Cᵒᵖ) : T.obj c = ⊤_ (Type u) := by refl
instance T_unique (c : Cᵒᵖ) : unique (T.obj c) := by rw T_proj; apply_instance 


def T_from (X : °C) : X ⟶ T := { app := λ _ _, default }

instance T_hom_unique (X : °C) : unique (X ⟶ T) := 
{ default := T_from X,
  uniq := 
  begin
    intro, apply nat_trans.ext,
    funext, simp
  end }

lemma T_is_terminal : is_terminal (@T C _ _) := is_terminal.of_unique _
lemma T_iso : T ≅ ₸ := is_terminal.unique_up_to_iso T_is_terminal terminal_is_terminal


/- A (maybe) useful lemma, telling that we can transfer unicity along iso -/
lemma unique_iso {X Y : °C} (f : X ≅ Y) (c : Cᵒᵖ) : unique (X.obj c) → unique (Y.obj c) :=
begin
  intro h, resetI,
  refine { default := (iso.app f c).hom default, uniq := _},
  intro a, 
  apply ((is_iso_iff_bijective (iso.app f c).inv).elim_left _).left, 
  { simp },
  { resetI, apply_instance } 
end

/- Now, we show that the terminal presheaf has object the one element type -/
instance unique_obj (c : Cᵒᵖ) : unique (₸.obj c) := unique_iso T_iso c (terminal.T_unique c)

-- weirdly, this is needed, because we cannot write directly (terminal.from X).app, I don't know why
abbreviation terminal_from (X : °C) : X ⟶ ⊤_ °C:= terminal.from X

@[simp] lemma terminal_app (X : °C) (c : Cᵒᵖ) (x : X.obj c): ((terminal_from X).app c) x = default := by dec_trivial

end terminal

namespace pullback
/-
  Here we show that pullbacks are computed pointwise in °C, so we have 
  a cartesian square of natural transformation iff for each c : Cᵒᵖ the 
  "applied" square is a pullback. 
  As a consequence a natural transormation is mono iff each component are mono

  Notation :
  W --v--> Y
  |        |
  u        t
  |        |
  X --s--> Z
  We show that we have an isomorphism of pullback cones, between the applied pullback cone in c
  and the canonical pullback cone from s_c and t_c. 
-/

variables {X Y Z : °C} (s : X ⟶ Z) (t : Y ⟶ Z) (c : Cᵒᵖ)

lemma cospan_flip (c : Cᵒᵖ) : (cospan s t).flip.obj c = cospan (s.app c) (t.app c) :=
begin
  apply category_theory.functor.ext,
  swap,
  { intro x, cases x,
    { refl },
    { cases x; refl, } },
  { intros x y f, cases f,
    { dsimp, simp }, --erw (functor.flip_obj_obj (cospan s t) c x) },
    { cases f_1; refl } }
end

lemma pullback_flip : limit ((cospan s t).flip.obj c) = pullback (s.app c) (t.app c) :=
by rw cospan_flip

lemma pullback_flip' : limit ((cospan s t).flip.obj c) = limit (cospan (s.app c) (t.app c)) :=
by rw cospan_flip

-- If W is the pullback of s and t, then W(c) is iso to the pullback of s_c and t_c
lemma iso_app_X : (pullback s t).obj c ≅ pullback (s.app c) (t.app c) := 
begin
  rw ←pullback_flip,
  dunfold pullback,
  change limit ((cospan s t).flip.obj c) with lim.obj ((cospan s t).flip.obj c),
  rw ←functor.comp_obj, simp,
  exact (limit_iso_flip_comp_lim (cospan s t)).app c,
end

lemma iso_app_of_is_limit (c : Cᵒᵖ) (w : pullback_cone s t) (hw : is_limit w) 
  (wc : pullback_cone (s.app c) (t.app c)) (hwc : is_limit wc) : w.X.obj c ≅ wc.X :=
begin
  apply iso.trans ((is_limit.cone_point_unique_up_to_iso hw (limit.is_limit _)).app c),
  apply iso.trans _ (is_limit.cone_point_unique_up_to_iso hwc (limit.is_limit _)).symm,
  exact iso_app_X s t c,
end

/-
  We constuct an explicit cone isomorphim between the pullback cone of s_c and t_c
  and the (pullback cone of s and t)_c  
-/

abbreviation pullback_fst_app : (pullback s t).obj c ⟶ X.obj c := 
(pullback.fst : pullback s t ⟶ X).app c
abbreviation pullback_snd_app : (pullback s t).obj c ⟶ Y.obj c := 
(pullback.snd : pullback s t ⟶ Y).app c

lemma iso_app_comm : 
  pullback_fst_app s t c ≫ s.app c = pullback_snd_app s t c ≫ t.app c :=
begin 
  rw [←nat_trans.vcomp_app, ←nat_trans.vcomp_app, nat_trans.vcomp_eq_comp, pullback.condition], 
  refl
end

def app_cone : pullback_cone (s.app c) (t.app c) := 
  pullback_cone.mk (pullback_fst_app s t c) (pullback_snd_app s t c) (iso_app_comm s t c)

@[simp] lemma eval_obj_eq_simp (x : walking_cospan) : 
  (cospan (s.app c) (t.app c)).obj x = (cospan s t ⋙ (evaluation Cᵒᵖ (Type u)).obj c).obj x :=
begin
  cases x; simp, cases x; simp,
end

@[simp] lemma eval_obj_eq_simp' (x : walking_cospan) : 
  (cospan (s.app c) (t.app c)).obj x = ((cospan s t).obj x).obj c := by simp

@[simp] lemma eval_map_eq_simp (x y : walking_cospan) (f : x ⟶ y) :
  (cospan (s.app c) (t.app c)).map f = 
  (eq_to_hom (eval_obj_eq_simp' _ _ _ x)) ≫ ((cospan s t).map f).app c ≫ 
    (eq_to_hom (eval_obj_eq_simp' _ _ _ y).symm) :=
begin
  cases f, cases x, refl, cases x; refl,
  cases f_1; refl,
end

@[simp] lemma cospan_evaluation : 
  cospan s t ⋙ (evaluation Cᵒᵖ (Type u)).obj c = cospan (s.app c) (t.app c) :=
begin
  symmetry,
  apply category_theory.functor.ext,
  swap,
  { simp, },
  { intros x y f, rw eval_map_eq_simp, refl }
end


lemma coerce_pullback_limit_evaluation : 
  limit (cospan s t ⋙ (evaluation Cᵒᵖ (Type u)).obj c) = pullback (s.app c) (t.app c) :=
by simp only [cospan_evaluation]

-- The cone isomorphism we use to show pullback are computed pointwise 
def iso_app_cone_X := (limit_obj_iso_limit_comp_evaluation (cospan s t) c) ≪≫
                eq_to_iso (coerce_pullback_limit_evaluation s t c)

lemma iso_fst_comm : pullback_fst_app s t c = 
  (iso_app_cone_X s t c).hom ≫ (pullback.fst : pullback (s.app c) (t.app c) ⟶ X.obj c) :=
begin
  unfold iso_app_cone_X, simp,
  dunfold pullback_fst_app, symmetry,
  convert limit_obj_iso_limit_comp_evaluation_hom_π (cospan s t) walking_cospan.left c, 
  dunfold pullback.fst, 
  rw ←id_comp (limit.π (cospan s t ⋙ (evaluation Cᵒᵖ (Type u)).obj c) walking_cospan.left),
  rw ←eq_to_hom_refl,
  congr; simp, refl
end

lemma iso_snd_comm : pullback_snd_app s t c = 
  (iso_app_cone_X s t c).hom ≫ (pullback.snd : pullback (s.app c) (t.app c) ⟶ Y.obj c) :=
begin
  unfold iso_app_cone_X, simp,
  dunfold pullback_snd_app, symmetry,
  convert limit_obj_iso_limit_comp_evaluation_hom_π (cospan s t) walking_cospan.right c, 
  dunfold pullback.snd, 
  rw ←id_comp (limit.π (cospan s t ⋙ (evaluation Cᵒᵖ (Type u)).obj c) walking_cospan.right),
  rw ←eq_to_hom_refl,
  congr; simp, refl
end

@[simp] lemma app_cone_X : (app_cone s t c).X = (limit (cospan s t)).obj c  := by refl
@[simp] lemma pulback_cone_X : 
  (limit.cone (cospan (s.app c) (t.app c))).X = pullback (s.app c) (t.app c) := by refl

def iso_app_cone_X' : (app_cone s t c).X ≅ (limit.cone (cospan (s.app c) (t.app c))).X :=
begin
simp, exact iso_app_cone_X s t c
end

-- This is the isomorphism
def iso_app_cone : app_cone s t c ≅ limit.cone (cospan (s.app c) (t.app c)) :=
begin
  unfold app_cone,
  apply pullback_cone.ext (iso_app_cone_X' s t c) (iso_fst_comm s t c) (iso_snd_comm s t c),
end

lemma app_cone_is_limit : is_limit (app_cone s t c) := 
is_limit.of_iso_limit (limit_cone.is_limit _) (iso_app_cone s t c).symm

-- More generally, we can get an iso of cone from a any limit cone
lemma iso_app_cone_of_is_limit (wc : pullback_cone (s.app c) (t.app c)) (hwc : is_limit wc) : 
  app_cone s t c ≅ wc := 
begin
exact is_limit.unique_up_to_iso (app_cone_is_limit s t c) hwc
end

lemma app_cone_of_cone_comm {s : X ⟶ Z} {t : Y ⟶ Z} (w : pullback_cone s t) (c : Cᵒᵖ) :
  w.fst.app c ≫ s.app c = w.snd.app c ≫ t.app c := 
begin
  rw [←nat_trans.vcomp_app, ←nat_trans.vcomp_app, nat_trans.vcomp_eq_comp, 
      pullback_cone.condition w],
  refl
end

variables {s t}
def app_cone_of_cone (w : pullback_cone s t) (c : Cᵒᵖ) := 
  pullback_cone.mk (w.fst.app c) (w.snd.app c) (app_cone_of_cone_comm w c)

@[simp] lemma app_cone_cano : 
  app_cone_of_cone (pullback_cone.mk pullback.fst pullback.snd pullback.condition) c = app_cone s t c := by refl

def app_cone_iso_of_iso_cone_X (w w' : pullback_cone s t) (c : Cᵒᵖ) (i : w ≅ w') :
  (app_cone_of_cone w c).X ≅ (app_cone_of_cone w' c).X :=
{ hom := i.hom.hom.app c, 
  inv := i.inv.hom.app c,
  hom_inv_id' := 
  begin
   rw ←nat_trans.vcomp_app, rw nat_trans.vcomp_eq_comp, 
   change i.hom.hom ≫ i.inv.hom with (i.hom ≫ i.inv).hom,
   simp, refl,
  end,
  inv_hom_id' := 
  begin
   rw ←nat_trans.vcomp_app, rw nat_trans.vcomp_eq_comp, 
   change i.inv.hom ≫ i.hom.hom with (i.inv ≫ i.hom).hom,
   simp, refl,
  end }

lemma app_cone_fst (w : pullback_cone s t) (c : Cᵒᵖ) : 
  (w.π.app walking_cospan.left).app c = (app_cone_of_cone w c).fst := by refl

lemma app_cone_snd (w : pullback_cone s t) (c : Cᵒᵖ) : 
  (w.π.app walking_cospan.right).app c = (app_cone_of_cone w c).snd := by refl

lemma app_cone_iso_of_iso_cone_fst_comm (w w' : pullback_cone s t) (c : Cᵒᵖ) (i : w ≅ w') : 
  (app_cone_of_cone w c).fst = 
  (app_cone_iso_of_iso_cone_X w w' c i).hom ≫ (app_cone_of_cone w' c).fst :=
begin
  change (app_cone_iso_of_iso_cone_X w w' c i).hom with i.hom.hom.app c,
  rw [←app_cone_fst w, ←app_cone_fst w', ←nat_trans.vcomp_app, 
      nat_trans.vcomp_eq_comp, i.hom.w' walking_cospan.left]
end

lemma app_cone_iso_of_iso_cone_snd_comm (w w' : pullback_cone s t) (c : Cᵒᵖ) (i : w ≅ w') : 
  (app_cone_of_cone w c).snd = 
  (app_cone_iso_of_iso_cone_X w w' c i).hom ≫ (app_cone_of_cone w' c).snd :=
begin
  change (app_cone_iso_of_iso_cone_X w w' c i).hom with i.hom.hom.app c,
  rw [←app_cone_snd w, ←app_cone_snd w', ←nat_trans.vcomp_app, 
      nat_trans.vcomp_eq_comp, i.hom.w' walking_cospan.right]
end

lemma app_cone_iso_of_iso_cone (w w' : pullback_cone s t) (c : Cᵒᵖ) (i : w ≅ w') : 
  (app_cone_of_cone w c) ≅ (app_cone_of_cone w' c) :=
pullback_cone.ext (app_cone_iso_of_iso_cone_X w w' c i) 
                  (app_cone_iso_of_iso_cone_fst_comm w w' c i) 
                  (app_cone_iso_of_iso_cone_snd_comm w w' c i)


-- Useful result : if a cone is limit in the preshea world, then every applied cone is limit
lemma is_limit_app_cone_of_cone (w : pullback_cone s t) (hw : is_limit w) (c : Cᵒᵖ) :
  is_limit (app_cone_of_cone w c) :=
begin
  have g := app_cone_iso_of_iso_cone _ w c (is_limit.unique_up_to_iso (pullback_is_pullback s t) hw),
  simp at g,
  apply is_limit.of_iso_limit (app_cone_is_limit s t c) g,
end

end pullback

-- Some problems see:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Category.20Type
-- local attribute [-instance]
--   limits.has_kernel_pair_of_mono
--   limits.has_pullback_of_left_factors_mono
--   limits.has_pullback_of_right_factors_mono
--   limits.has_pullback_of_comp_mono

lemma mono_app_of_mono {S X : °C} (m : S ⟶ X) [mono m] (c : Cᵒᵖ) : mono (m.app c) :=
begin 
  apply pullback_cone.mono_of_is_limit_mk_id_id,
  exact pullback.is_limit_app_cone_of_cone _ (pullback_cone.is_limit_mk_id_id m) c,
end

namespace classifier
variables {S X : °C} (m : S ⟶ X) [mono m]

/- The classifiyng arrow of m : S ⟶ X is the sieve
  χ_c(x) = {g : d ⟶ c | ∃ y : S(d), m_d(y) = X(g)(x) }
-/
def χ_app (c : Cᵒᵖ) (x : X.obj c) : sieve c.unop := 
{ arrows := λ d f, ∃ (y : S.obj (opposite.op d)), m.app (opposite.op d) y = X.map f.op x, 
  downward_closed' := 
  begin
  intros d e f h g,
  cases h with w hw,
  use S.map (g.op) w,
  rw [op_comp, functor_to_types.naturality, hw, functor.map_comp'], refl
  end
}

def χ : X ⟶ Ω := 
{ app := χ_app m,
  naturality' := 
  begin
    intros c d f,   
    funext, dsimp,
    ext1, fsplit;
    { intro a, cases a, fsplit, exact a_w, rw [op_comp, functor.map_comp'] at *, assumption },
  end }

lemma pullback_condition : m ≫ χ m = terminal.from S ≫ truth :=
begin
  ext1, funext c x, simp, apply sieve.ext,
  intros d f, simp, 
  use S.map f.op x, 
  rw functor_to_types.naturality, dsimp, refl
end

def pb_cone : pullback_cone (χ m) truth := pullback_cone.mk m (terminal.from S) (pullback_condition m)

def pb_lift (u : pullback_cone (χ m) truth) : u.X ⟶ S := sorry
lemma is_limit_pb_cone : is_limit (pb_cone m) := 
begin
sorry -- apply pullback_cone.is_limit.mk

end

end classifier


end presheaf
instance has_subobject_classifier_hatC : has_subobject_classifier °C :=
begin
  sorry
end


-- instance topos_hatC : topos °C := topos.mk
 