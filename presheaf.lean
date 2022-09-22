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


variables (C : Type u) [category.{u} C] [small_category C]

local notation `°`:std.prec.max_plus C := Cᵒᵖ ⥤ Type u
local notation `₸` := ⊤_ (°C)

namespace presheaf
variable {C}
-- (C ⥤ (Type u)ᵒᵖ) 

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
@[simp] lemma truth_app (c : Cᵒᵖ) (x : ₸.obj c) : (truth C).app c x = ⊤ := by refl

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
/- Let us prove that the terminal object in Type u is iso the one element type -/

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
instance unique_obj (c : Cᵒᵖ) : unique (₸.obj c) := unique_iso (T_iso C) c (terminal.T_unique c)

-- weirdly, this is needed, because we cannot write directly (terminal.from X).app, I don't know why
abbreviation terminal_from (X : °C) : X ⟶ ⊤_ °C:= terminal.from X

@[simp] lemma terminal_app (X : °C) (c : Cᵒᵖ) (x : X.obj c): ((terminal_from X).app c) x = default := by dec_trivial

end terminal

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

lemma pullback_condition : m ≫ χ m = terminal.from S ≫ truth C :=
begin
  ext1, funext, simp, 
end

end classifier


end presheaf
instance has_subobject_classifier_hatC : has_subobject_classifier °C :=
begin
  sorry
end


-- instance topos_hatC : topos °C := topos.mk
 