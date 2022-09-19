import category_theory.limits.shapes.finite_limits
import category_theory.closed.cartesian
import category_theory.subobject.basic
import category_theory.subobject.lattice

import order.heyting.basic

import topos
import subobject_classifier
import pullbacks
import image

open category_theory category_theory.category category_theory.limits classifier

universes v u

noncomputable theory

variables (C : Type u) [category.{v} C ]

variables [topos.{v} C] [has_finite_colimits.{v} C]


/- We now define the arrow for the Heyting structure on the suboject of Ω, 
   we could have done it for any object X, but we keep it simple
-/
variables (C)
/-- ⊤ is the classifing arrow of the identity, hence it is truth -/
def top_arrow : ⊤_ C ⟶ Ω C:= classifier_of (𝟙 ⊤_ C)

@[simp] lemma top_arrow_eq_truth : top_arrow C = truth C :=
begin
unfold top_arrow, rw uniquely (𝟙 ⊤_ C), exact truth_classifies_id C
end

/-- Could have been terminal.from ⊥_ C -/
def bot_arrow : ⊤_ C ⟶ Ω C := classifier_of (initial.to (⊤_ C))

/- We define the ∧ arrow Ω ⨯ Ω ⟶ Ω  -/
def ΩxΩ : C := (Ω C) ⨯ (Ω C)
def truth_truth : ⊤_ C ⟶ (Ω C) ⨯ (Ω C) := prod.lift (truth C) (truth C)
def and_arrow : ΩxΩ C ⟶ Ω C := classifier_of (truth_truth C)

/- For the implication, we first define ≤, and take its classyfing arrow -/
def leq_arrow := equalizer.ι (limits.prod.fst : ΩxΩ C ⟶ Ω C) (and_arrow C)
instance mono_leq : mono.{v} (leq_arrow C) := equalizer.ι_mono.

def imp_arrow : ΩxΩ C ⟶ Ω C := classifier_of (leq_arrow C)

/- For the or, we need some more work -/
def id_true : Ω C ⟶ ΩxΩ C := prod.lift (𝟙 (Ω C)) (terminal.from (Ω C) ≫ truth C)
def true_id : Ω C ⟶ ΩxΩ C := prod.lift (terminal.from (Ω C) ≫ truth C) (𝟙 (Ω C))
def or_lift : Ω C ⨿ Ω C ⟶ ΩxΩ C := coprod.desc (id_true C) (true_id C) 

def or_facto := image.canonical_factorisation (or_lift C)
def or_arrow : ΩxΩ C ⟶ Ω C := classifier_of (or_facto C).m

/- The ¬ is implication to the negation -/
def neg_arrow : Ω C ⟶ Ω C := (prod.lift (𝟙 (Ω C)) (terminal.from (Ω C) ≫ bot_arrow C)) ≫ imp_arrow C

/- The equality -/
def δ (Y : C) : Y ⨯ Y ⟶ Ω C := classifier_of (diag Y) 


/- Now we interpret inductively any 1st order formula using the above arrow -/
variables {C} {X : C} 

/- Now we can write formulas and prove the Heyting structure -/
instance has_bot_X_to_Ω : has_bot (X ⟶ Ω C) :=  { bot := terminal.from X ≫ bot_arrow C}
instance has_top_X_to_Ω : has_top (X ⟶ Ω C) :=  { top := terminal.from X ≫ top_arrow C}
instance has_and_X_to_Ω : has_inf (X ⟶ Ω C) := { inf := λ σ τ, prod.lift σ τ ≫ and_arrow C }
instance has_or_X_to_Ω : has_sup(X ⟶ Ω C) := { sup :=  λ σ τ, prod.lift σ τ ≫ or_arrow C }
instance has_imp_X_to_Ω : has_himp (X ⟶ Ω C) := { himp := λ σ τ, prod.lift σ τ ≫ imp_arrow C}        
instance has_neg_X_to_Ω : has_hnot (X ⟶ Ω C) := { hnot := λ σ, σ ≫ neg_arrow C}  

/- Now, we define the same structure on the suboject, mathlib already proves it has a lattice structure -/
namespace heyting_sub

instance has_top_sub : has_top (subobject X) := { top := subobject.mk (𝟙 X) }
instance has_himp_sub : has_himp (subobject X) := 
{ himp := λ u v : subobject X, 
          subobject.mk (canonical_incl ((classifier_of u.arrow)⇨(classifier_of v.arrow))) }

end heyting_sub

/-! We show that the big squares are pullback using pasting lemmas -/

/- Top
  X ---> 1 ---> 1
  |      |      |
  |      |      |
  X ---> 1 ---> Ω
-/
variables (X)
def pullback_cone_top_left : pullback_cone (terminal.from X) (𝟙 (⊤_ C))  := 
pullback_cone.mk (𝟙 X) (terminal.from X)  (by simp)

lemma is_pullback_top_left : is_limit (pullback_cone_top_left X) := 
begin
  apply pullback_cone.is_limit.mk; intro s; simp
end

def pullback_cone_top_big : pullback_cone (⊤ : X ⟶ Ω C) (truth C)  := 
pullback_cone.mk (𝟙 X) (terminal.from X)  ( 
begin
  simp,
  rw [←terminal.comp_from (terminal.from X), assoc], 
  change terminal.from (⊤_ C) ≫ truth C with lift_truth _, 
  rw [←(pb_classifier_condition (𝟙 (⊤_ C))), id_comp],
  refl
end)

lemma is_pullback_top_big : is_limit (pullback_cone_top_big X) :=
begin
  have h := (comp_id (terminal.from X)),
  unfold pullback_cone_top_big, 
  conv in (terminal.from X) { rw ← h },
  refine big_square_is_pullback (terminal.from X) (𝟙 (⊤_ C)) (terminal.from X) (top_arrow C) (𝟙 X)
   (𝟙 (⊤_ C)) (truth C) (by simp) (by simp) _ _,
  { rw top_arrow_eq_truth C at *,
    convert @classifying_pullback.is_pb _ _ _ _ _ _ _ _ _ _,
    { exact (is_terminal.from_self terminal_is_terminal).symm },
    { rw top_arrow_eq_truth,
      exact (truth_classifies_id C) } },
  { exact is_pullback_top_left X }
end

/- Bot
  0 ---> 0 ---> 1
  |      |      |
  |      |      |
  X ---> 1 ---> Ω
-/
def pullback_cone_bot_left : pullback_cone (terminal.from X) (terminal.from ⊥_ C) := 
pullback_cone.mk (initial.to X) (𝟙 (⊥_ C)) (by simp)

lemma is_pullback_bot_left : is_limit (pullback_cone_bot_left X) := 
begin
  apply pullback_cone.is_limit.mk _ (λ s, s.snd); simp, 
  intro s, rw ← (initial.to_comp s.fst),
  -- in a CCC, the initial is strict, meaning s ≅ ⊥_ whenever we have u : s ⟶ ⊥_
  -- that's how we prove the left square is a pullback
  suffices h : s.snd ≫ initial.to s.X = 𝟙 s.X, 
  { rw [←assoc, h], simp },
  { rw [←category_theory.is_iso.hom_inv_id s.snd, cancel_epi s.snd],
   apply is_initial.hom_ext _ _ _ , exact initial_is_initial }
  -- { intros s m _ _, 
  --   exact is_initial.hom_ext (is_initial.of_iso (initial_is_initial) (as_iso m).symm) m s.fst }
end

def pullback_cone_bot_big : pullback_cone (⊥ : X ⟶ Ω C) (truth C) := 
pullback_cone.mk (initial.to X) (𝟙 (⊥_ C) ≫ terminal.from (⊥_ C)) (by simp)

lemma is_pullback_bot_big : is_limit (pullback_cone_bot_big X) := 
begin
  unfold pullback_cone_bot_big,
  refine big_square_is_pullback (𝟙 (⊥_ C)) (terminal.from (⊥_ C)) 
        (terminal.from X) (bot_arrow C) (initial.to X) 
        (terminal.from ⊥_ C) (truth C) (by simp) (by simp) _ _,
  { apply classifying_pullback.is_pb, 
    have g : terminal.from (⊥_ C) = initial.to (⊤_ C) := by simp,
    rw g,  exact (classifies (initial.to (⊤_ C))) },
  { exact (is_pullback_bot_left X) }
end

/- We show that the internal operators corresponds to the externals one -/
namespace ext_iso_int

lemma top : ↑(⊤ : subobject X) ≅ s{ (⊤ : X ⟶ Ω C) }s :=
begin
  let top_sub := (⊤ : subobject X),
  have h : terminal.from (top_sub : C) ≫ (truth C) = top_sub.arrow ≫ (⊤ : X ⟶ Ω C) :=
  begin
  sorry
  end,
  -- TODO show that both objects are pullbacks and thus are iso.
  -- have g := is_pullback_top_big (top_sub : C),
  -- have h := is_pullback_top_big s{(⊤ : X ⟶ Ω C)}s,
  -- have XX : (pullback_cone_top_big s{(⊤ : X ⟶ Ω C)}s).X = s{(⊤ : X ⟶ Ω C)}s := sorry,
  -- have YY : (pullback_cone_top_big (top_sub : C)).X = (top_sub : C) := sorry,
  -- rw [←XX, ←YY],
  -- convert @is_limit.cone_point_unique_up_to_iso _ _ _ _ _ _ _ g h,
  sorry
end


end ext_iso_int
-- lemma le_top (S : subobject X) : S ≤ (⊤ : subobject X) := 
-- begin
--   apply le_of_inf_eq, apply subobject.eq_of_comm, 
-- end

