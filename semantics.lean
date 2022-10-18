import category_theory.limits.shapes.finite_limits
import category_theory.closed.cartesian
import category_theory.subobject.basic
import category_theory.subobject.lattice

import order.heyting.basic

import topos
import subobject_classifier
import pullbacks
import image
import presheaf

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
abbreviation ΩxΩ : C := (Ω C) ⨯ (Ω C)
abbreviation truth_truth : ⊤_ C ⟶ (Ω C) ⨯ (Ω C) := prod.lift (truth C) (truth C)
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
instance has_or_X_to_Ω : has_sup (X ⟶ Ω C) := { sup :=  λ σ τ, prod.lift σ τ ≫ or_arrow C }
instance has_imp_X_to_Ω : has_himp (X ⟶ Ω C) := { himp := λ σ τ, prod.lift σ τ ≫ imp_arrow C}        
instance has_neg_X_to_Ω : has_hnot (X ⟶ Ω C) := { hnot := λ σ, σ ≫ neg_arrow C}  

lemma simp_top : terminal.from X ≫ truth C = ⊤ := begin
  rw ←top_arrow_eq_truth, refl,
end

/- Now, we define the same structure on the suboject, mathlib already proves it is a lattice -/
namespace heyting_sub

instance has_top_sub : has_top (subobject X) := { top := subobject.mk (𝟙 X) }
instance has_himp_sub : has_himp (subobject X) := 
{ himp := λ u v : subobject X, 
          subobject.mk (canonical_incl ((classifier_of u.arrow)⇨(classifier_of v.arrow))) }

-- To prove it has bot, we just need to prove the morphism from initial is mono
instance initial_mono_class_topos : initial_mono_class C := 
initial_mono_class.of_is_initial (initial_is_initial) (λ _ , initial_mono _ (initial_is_initial))


variable (X)
lemma top_sub_iso_id : ↑(⊤ : subobject X) ≅ X := subobject.underlying_iso _
lemma bot_sub_iso_init : ↑(⊥ : subobject X) ≅ ⊥_ C := subobject.underlying_iso _

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

namespace and_useless
variables {X} (σ τ : X ⟶ Ω C)
-- Well this is not what we want, but I realized that too late, so it's here anyway
/- And
  {σ}x{τ} --->  1 ----> 1
     |          |       |
     |          |       |
    XxX -----> ΩxΩ ---> Ω
-/
open category_theory.limits.prod

lemma map_to_terminal_eq_terminal_from_lift {X Y: C} (f : ⊤_ C ⟶ X) (g : ⊤_ C ⟶ Y) :
  map f g = terminal.from (⊤_ C ⨯ ⊤_ C) ≫ lift f g :=
begin
  rw comp_lift,
  nth_rewrite 0 is_terminal.hom_ext (terminal_is_terminal) (terminal.from (⊤_ C ⨯ ⊤_ C)) fst,
  rw [is_terminal.hom_ext (terminal_is_terminal) (terminal.from (⊤_ C ⨯ ⊤_ C)) snd,
      lift_fst_comp_snd_comp]
end

lemma commutation_big_square : 
  map (canonical_incl σ) (canonical_incl τ) ≫ map σ τ = 
  terminal.from (s{σ}s ⨯ s{τ}s) ≫ truth_truth C :=
begin
have g := is_terminal.hom_ext terminal_is_terminal (terminal.from _) 
          (map (terminal.from s{σ}s) (terminal.from s{τ}s) ≫ terminal.from _), 
rw [map_map, canonical_incl_comm σ, canonical_incl_comm τ, ←map_map,
    g, assoc, map_to_terminal_eq_terminal_from_lift]; refl
end

      
def pullback_cone_and_left : pullback_cone (map σ τ) (truth_truth C) := 
pullback_cone.mk (map (canonical_incl σ) (canonical_incl τ)) (terminal.from _) 
                 (commutation_big_square _ _)

variables {σ τ}
def induced_cone_left (s : pullback_cone (map σ τ) (truth_truth C)) :
  pullback_cone σ (truth C) := pullback_cone.mk (s.fst ≫ fst) (terminal.from _)
  (by rw [assoc, ←map_fst _ τ, ←assoc, s.condition, assoc, lift_fst,
          is_terminal.hom_ext terminal_is_terminal (s.snd)])

def induced_cone_right (s : pullback_cone (map σ τ) (truth_truth C)) :
  pullback_cone τ (truth C) := pullback_cone.mk (s.fst ≫ snd) (terminal.from _)
  (by rw [assoc, ←map_snd σ τ, ←assoc, s.condition, assoc, lift_snd,
          is_terminal.hom_ext terminal_is_terminal (s.snd)])

def lift_of_cone {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (s : pullback_cone f g) : 
  s.X ⟶ pullback f g := pullback.lift s.fst s.snd s.condition

def induced_lift (s : pullback_cone (map σ τ) (truth_truth C)) : s.X ⟶ s{σ}s ⨯ s{τ}s :=  
lift (lift_of_cone (induced_cone_left s)) (lift_of_cone (induced_cone_right s))

variables (σ τ)
lemma is_pullback_and_left : is_limit (pullback_cone_and_left σ τ) :=
begin
  apply pullback_cone.is_limit.mk _ (λ s, induced_lift s); intro s,
  { simp only, erw lift_map, apply hom_ext,
      rw lift_fst, dunfold induced_cone_left lift_of_cone, rw pullback.lift_fst, refl,
      rw lift_snd, dunfold lift_of_cone, rw pullback.lift_fst, refl
  },
  { apply is_terminal.hom_ext (terminal_is_terminal) },
  { intros m hfst hsnd, simp only, clear hsnd,
    apply hom_ext; apply pullback.hom_ext; try { apply is_terminal.hom_ext terminal_is_terminal },
    { have hfst_fst := eq_whisker hfst fst, 
      rw [assoc, map_fst, ←assoc] at hfst_fst,
      erw [hfst_fst, lift_fst, pullback.lift_fst], refl },
    { have hfst_snd := eq_whisker hfst snd, 
      rw [assoc, map_snd, ←assoc] at hfst_snd,
      erw [hfst_snd, lift_snd, pullback.lift_fst], refl } }
end


def pullback_cone_and_big : pullback_cone (map σ τ ≫ and_arrow C) (truth C) := 
pullback_cone.mk (map (canonical_incl σ) (canonical_incl τ)) (terminal.from _ ≫ terminal.from (⊤_ C)) 
  (by { rw [←assoc, commutation_big_square σ τ, assoc, assoc], 
        unfold and_arrow, rw [classifier.comm ] }) 

lemma is_pullback_and_big : is_limit (pullback_cone_and_big σ τ) := 
begin
  unfold pullback_cone_and_big,
  refine big_square_is_pullback (terminal.from _) (terminal.from _) 
        (map σ τ) (and_arrow C) (map (canonical_incl σ) (canonical_incl τ)) 
        (truth_truth C) (truth C) (by rw commutation_big_square) (by erw classifier.comm) _ _,
  { apply classifying_pullback.is_pb, unfold and_arrow, apply classifies },
  { exact (is_pullback_and_left σ τ) }
end

end and_useless


/- We show that the internal operators corresponds to the external ones -/
namespace external_iso_internal

-- TOP
variable (X)
lemma top_sub : (⊤ : subobject X) = canonical_sub ⊤ := 
begin 
  ext1, 
  exact is_limit.cone_point_unique_up_to_iso_hom_comp (is_pullback_top_big X) 
                                                      (pullback_is_pullback _ _) 
                                                       walking_cospan.left 
end

def top : ↑(⊤ : subobject X) ≅ s{ (⊤ : X ⟶ Ω C) }s := 
iso.trans (subobject.iso_of_eq _ _ (top_sub X)) (canonical_sub_iso_canonical ⊤)

def top' : X ≅ s{ (⊤ : X ⟶ Ω C) }s := iso.trans (heyting_sub.top_sub_iso_id X).symm (top X) 


-- BOT
lemma bot_sub : (⊥ : subobject X) = canonical_sub ⊥ := 
begin 
  ext1, 
  exact is_limit.cone_point_unique_up_to_iso_hom_comp (is_pullback_bot_big X) 
                                                      (pullback_is_pullback _ _) 
                                                       walking_cospan.left 
end

def bot : ↑(⊥ : subobject X) ≅ s{ (⊥ : X ⟶ Ω C) }s := 
iso.trans (subobject.iso_of_eq _ _ (bot_sub X)) (canonical_sub_iso_canonical ⊥)

def bot' : ⊥_ C ≅ s{ (⊥ : X ⟶ Ω C) }s := iso.trans (heyting_sub.bot_sub_iso_init X).symm (bot X) 


-- AND
variables {X} (σ τ : X ⟶ Ω C)

open category_theory.limits.prod
/-
  {σ ⊓ τ}------>  1 -------> 1
    |             |          |
    |             |          |
    X --(σ, τ)-> ΩxΩ ---∧--> Ω 

-/
-- In the above, the big square and right sqaure are pullbacks, so is the left

lemma left_square_commutes : canonical_incl (σ ⊓ τ) ≫ lift σ τ = terminal.from _ ≫ truth_truth C :=
begin
  have comm := canonical_incl_comm (σ ⊓ τ),
  erw ←assoc at comm, 
  rw ← (pullback_cone.is_limit.lift' (classifier.is_pb (truth_truth C)) 
        (canonical_incl (σ ⊓ τ) ≫ lift σ τ) (terminal.from _) comm).prop.left,
  congr, apply is_terminal.hom_ext terminal_is_terminal,
end

lemma left_square_commutes_fst : canonical_incl (σ ⊓ τ) ≫ σ = terminal.from _ ≫ truth C :=
begin
  have g := eq_whisker (left_square_commutes σ τ) fst,
  rwa [assoc, assoc, lift_fst, lift_fst] at g,
end

lemma left_square_commutes_snd : canonical_incl (σ ⊓ τ) ≫ τ = terminal.from _ ≫ truth C :=
begin
  have g := eq_whisker (left_square_commutes σ τ) snd,
  rwa [assoc, assoc, lift_snd, lift_snd] at g,
end

def left_lift : s{σ ⊓ τ}s ⟶ s{σ}s :=  
pullback.lift (canonical_incl (σ ⊓ τ)) (terminal.from _) (left_square_commutes_fst _ _)

def right_lift : s{σ ⊓ τ}s ⟶ s{τ}s :=  
pullback.lift (canonical_incl (σ ⊓ τ)) (terminal.from _) (left_square_commutes_snd _ _)

-- A cone of apex s{σ ⊓ τ}s, we will show it is a pullback
-- and thus have our cone isomorphism
def internal_cone : pullback_cone (canonical_incl σ) (canonical_incl τ) :=
pullback_cone.mk (left_lift σ τ) (right_lift σ τ) (by {erw [pullback.lift_fst, pullback.lift_fst]})

@[simp] lemma internal_cone_X : (internal_cone σ τ).X = s{σ ⊓ τ}s := rfl 

variables {σ τ}

def external_cone_to_internal_cone (u : pullback_cone (canonical_incl σ) (canonical_incl τ)) :
  pullback_cone (σ ⊓ τ) (truth C) := pullback_cone.mk (u.fst ≫ canonical_incl σ) (terminal.from _) 
  (begin
    rw assoc, nth_rewrite 1 ←assoc, 
    rw [comp_lift, ←assoc, comp_lift,
        canonical_incl_comm, ←assoc, terminal.comp_from,
        ←assoc, u.condition, assoc, canonical_incl_comm,
        ←assoc, terminal.comp_from, ←comp_lift, assoc],
    erw classifier.comm (truth_truth C), 
    rw [←assoc, terminal.comp_from],
   end)

def external_cone_to_internal_cone_fst (u : pullback_cone (canonical_incl σ) (canonical_incl τ)) :
  (external_cone_to_internal_cone u).fst = (u.fst ≫ canonical_incl σ) := rfl

def external_cone_to_internal_cone_snd (u : pullback_cone (canonical_incl σ) (canonical_incl τ)) :
  (external_cone_to_internal_cone u).fst = (u.snd ≫ canonical_incl τ) := 
begin
  rw ←u.condition,
  apply external_cone_to_internal_cone_fst
end

variables (σ τ)

lemma is_limit_internal_cone : is_limit (internal_cone σ τ) :=
begin
  apply pullback_cone.is_limit_aux',
  intro s,
  let l := (pullback_cone.is_limit.lift' (pullback_is_pullback (σ ⊓ τ) (truth C)) 
            (external_cone_to_internal_cone s).fst (external_cone_to_internal_cone s).snd
            (external_cone_to_internal_cone s).condition),
  use l.val, split, 
  dunfold internal_cone,
  { rw ←cancel_mono (canonical_incl σ),
    erw ←external_cone_to_internal_cone_fst,
    refine eq.trans _ l.prop.left, 
    rw assoc, congr, apply pullback.lift_fst },
  split,
  { rw ←cancel_mono (canonical_incl τ),
    erw ←external_cone_to_internal_cone_snd,
    refine eq.trans _ l.prop.left, 
    rw assoc, congr, apply pullback.lift_fst },
  { intros u fst_comm snd_comm, apply pullback.hom_ext,
    { symmetry, apply eq.trans l.prop.left, 
      rw [external_cone_to_internal_cone_fst, ←fst_comm, assoc],
      congr, erw pullback.lift_fst },
    { apply is_terminal.hom_ext (terminal_is_terminal) } }
end

-- The convention was not the same we we have the symmetric verion
lemma and_sub' : (canonical_sub τ) ⊓ (canonical_sub σ) = canonical_sub (σ ⊓ τ) :=
begin
  ext1, 
  have g := eq_whisker 
    (is_limit.cone_point_unique_up_to_iso_hom_comp 
      (pullback_is_pullback (canonical_incl σ) (canonical_incl τ)) 
      (is_limit_internal_cone σ τ) 
      walking_cospan.right) 
    (canonical_incl τ),
  erw [assoc, pullback.lift_fst] at g,
  exact g,
end

lemma and_sub : (canonical_sub σ) ⊓ (canonical_sub τ) = canonical_sub (σ ⊓ τ) :=
by rw [←and_sub', inf_comm]

lemma and : ↑ ((canonical_sub σ) ⊓ (canonical_sub τ)) ≅ s{ σ ⊓ τ }s :=
iso.trans (subobject.iso_of_eq _ _ (and_sub σ τ)) (canonical_sub_iso_canonical (σ ⊓ τ))

end external_iso_internal


namespace validity

/- Let σ : X ⟶ Ω, a formulat is valid whenever σ factors trought true, 
   i.e σ = truth_X 
-/
variable {X}

def is_valid (σ : X ⟶ Ω C) : Prop := σ = lift_truth X 

-- Two characterization of validity
lemma valid_iff_section (σ : X ⟶ Ω C) : is_valid σ ↔ (is_split_epi (canonical_incl σ)) := 
begin
  split;  intro h,
  { apply is_split_epi.mk',
    exact {section_ := pullback.lift (𝟙 X) (terminal.from X) (by simpa [h]) } },
  { unfold is_valid,
    rw [←id_comp σ, ←h.exists_split_epi.some.id, assoc, 
        canonical_incl_comm, ←assoc, terminal.comp_from] }
end

lemma valid_iff_is_iso (σ : X ⟶ Ω C) : is_valid σ ↔ is_iso (canonical_incl σ) :=  
begin
  split; rw valid_iff_section; intro h; resetI,
  { apply is_iso_of_mono_of_is_split_epi (canonical_incl σ) },
  { apply is_split_epi.of_iso (canonical_incl σ), }
end

-- Auxiliary lemma that should be in the subobject lib.
lemma is_iso_of_sub_eq_mk_iso {Y Z : C} {f : Y ⟶ X} [mono f] {g : Z ⟶ X} [is_iso g] 
  (eq : subobject.mk f = subobject.mk g) : is_iso f :=
begin
  have f_eq : f = (subobject.iso_of_mk_eq_mk _ _ eq).hom ≫ g := by simp,
  rw f_eq,
  apply is_iso.comp_is_iso,
end

lemma valid_iff_eq_sub_top (σ : X ⟶ Ω C) : is_valid σ ↔ (canonical_sub σ) = (⊤ : subobject X) :=
begin
  split,
  { rw is_valid, intro h, rw h,
    convert (external_iso_internal.top_sub X).symm,
    exact simp_top },
  { rw valid_iff_is_iso,
    exact is_iso_of_sub_eq_mk_iso}
end

end validity

