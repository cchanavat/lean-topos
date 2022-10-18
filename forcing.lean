import category_theory.category.basic

import topos
import subobject_classifier
import presheaf
import semantics

open category_theory category_theory.category category_theory.limits classifier 

universes v u

noncomputable theory


variables {C : Type u} [category.{u} C] [small_category C]


namespace forcing

local notation `°`:std.prec.max_plus C := Cᵒᵖ ⥤ Type u
local notation `₸` := ⊤_ (°C)

-- Abbreviation for Yoneda on objects and on maps
abbreviation yob (c : Cᵒᵖ) := yoneda.obj c.unop
abbreviation yom {c d : Cᵒᵖ} (f : c ⟶ d) : yob d ⟶ yob c := yoneda.map f.unop

structure forces {X : °C} (σ : X ⟶ Ω °C) {c : Cᵒᵖ} (x : yob c ⟶ X) :=
(lift : yob c ⟶ s{ σ }s)
(comm' : lift ≫ canonical_incl σ = x. obviously)

restate_axiom forces.comm'
attribute [simp, reassoc] forces.comm

@[ext]
protected lemma lift_ext {X : °C} (σ : X ⟶ Ω °C) {c : Cᵒᵖ} (x : yob c ⟶ X) : 
  Π {α β : forces σ x}, α.lift = β.lift → α = β
| ⟨Ra, _⟩ ⟨Sa, _⟩ rfl := rfl

instance subsingleton_forces {X : °C} (σ : X ⟶ Ω °C) {c : Cᵒᵖ} (x : yob c ⟶ X) : 
  subsingleton (forces σ x) :=
begin
  fsplit, intros, ext1,
  apply pullback.hom_ext,
  { rw [a.comm, b.comm] },
  { simp }
end

def pforces {X : °C} (σ : X ⟶ Ω °C) {c : Cᵒᵖ} (x : yob c ⟶ X) : Prop := 
  ∃ lift : yob c ⟶ s{ σ }s, lift ≫ canonical_incl σ = x 

variables {X : °C} (σ : X ⟶ Ω °C) {c : Cᵒᵖ} (x : yob c ⟶ X)

lemma forces_to_pforces {x : yob c ⟶ X} (α : forces σ x) : pforces σ x := ⟨α.lift, α.comm⟩
lemma pforces_to_forces {x : yob c ⟶ X} (α : pforces σ x) : forces σ x :=
{ lift := (classical.indefinite_description _ α).val,
  comm' := (classical.indefinite_description _ α).prop }

lemma pforces_of_valid (h : validity.is_valid σ) : pforces σ x :=
begin
  rw validity.valid_iff_is_iso at h,
  resetI,
  refine ⟨ x ≫ (as_iso (canonical_incl σ)).inv, _ ⟩,
  rw [assoc, as_iso_inv, is_iso.inv_hom_id, comp_id]
end

lemma valid_yoneda_iff_pforces : 
  pforces σ x ↔ validity.is_valid (x ≫ σ) :=
begin
  split,
  { intro h, cases h with w h, dunfold validity.is_valid,
    rw [←h, assoc, canonical_incl_comm, ←assoc, limits.terminal.comp_from w]
  },
  { intro h, dunfold validity.is_valid at h,
    exact ⟨pullback.lift x (terminal.from (yob c)) h, pullback.lift_fst _ _ _⟩ }
end

def π_el.obj (d : (X.elements)ᵒᵖ) := (category_of_elements.π X).obj d.unop
def π_el.map {d e : (X.elements)ᵒᵖ} (f : d ⟶ e) : π_el.obj e ⟶ π_el.obj d := 
(category_of_elements.π X).map f.unop

@[simp] lemma simp_el_yob (d : (X.elements)ᵒᵖ) : 
  (functor_to_representables X).obj d = yob (π_el.obj d) := 
begin
   unfold functor_to_representables π_el.obj,
   rw functor.comp_obj,
   simp
end
-- set_option trace.simp_lemmas true
def forall_pforces_to_cocone (u : ∀ (c : Cᵒᵖ) (x : yob c ⟶ X), forces σ x) : 
  cocone (functor_to_representables X) :=
{ X := s{ σ }s, 
  ι := { app := λ d, (u (π_el.obj d) ((cocone_of_representable X).ι.app d)).lift,
         naturality' := 
          begin
            intros d e f,
            dunfold functor_to_representables, 
            simp only [functor.comp_map, functor.left_op_map, category_of_elements.π_map, 
                       subtype.val_eq_coe, functor.const_obj_map],
            rw [@comp_id _ _ _ (s{σ}s), ←cancel_mono (canonical_incl σ), assoc, (u _ _).comm,
                (u _ _).comm, cocone_of_representable_ι_app, cocone_of_representable_ι_app],
            dsimp, ext, 
            simp only [functor_to_types.comp, yoneda_map_app, yoneda_sections_small_inv_app_apply, 
                       op_comp, quiver.hom.op_unop, functor_to_types.map_comp_apply], 
            rw f.unop.prop,
          end } }

@[simp] lemma test (u : ∀ (c : Cᵒᵖ) (x : yob c ⟶ X), forces σ x) (d : (functor.elements X)ᵒᵖ) : 
  (forall_pforces_to_cocone σ u).ι.app d = 
  (u (π_el.obj d) ((cocone_of_representable X).ι.app d)).lift := by { refl }

def forall_pforces_to_split_epi (u : ∀ (c : Cᵒᵖ) (x : yob c ⟶ X), forces σ x) : 
  split_epi (canonical_incl σ) := 
{ section_ := is_colimit.desc (colimit_of_representable X) (forall_pforces_to_cocone σ u),
  id' := 
  begin
    apply is_colimit.hom_ext (colimit_of_representable X),
    intro d, 
    rw @comp_id _ _ _ X,
    simp
  end
}

-- http://chanavat.site/files/lmfi-thesis.pdf Theorem 2.10 
lemma valid_iff_forall_pforces {X : °C} (σ : X ⟶ Ω °C) :
  validity.is_valid σ ↔ ∀ (c : Cᵒᵖ) (x : yob c ⟶ X), pforces σ x :=
begin
  split,
  { rw validity.valid_iff_is_iso, intros h c x, 
    cases h.out with incl_inv h,
    use x ≫ incl_inv,
    rw [assoc, h.right, comp_id] },
  { rw validity.valid_iff_section, intro u,
    fsplit, fsplit,
    exact forall_pforces_to_split_epi σ (λ c x, pforces_to_forces σ (u c x)) }
end

lemma monotonicity (h : forces σ x) {b : Cᵒᵖ} (f : c ⟶ b) : forces σ (yom f ≫ x) :=
{ lift := yom f ≫ h.lift,
  comm' := by rw [assoc, h.comm] }

def yob_terminal_iso_terminal [has_terminal C] : (yob (opposite.op (⊤_ C))) ≅ ₸ :=
begin
  rw [←as_empty_cone_X (⊤_ °C), ←as_empty_cone_X (yob (opposite.op (⊤_ C)))],
  apply is_limit.cone_point_unique_up_to_iso,
  { apply category_theory.limits.is_terminal.is_terminal_obj, exact terminal_is_terminal },
  { exact terminal_is_terminal }
end

lemma closed_valid_iff_forces_terminal [has_terminal C] (τ : ₸ ⟶ Ω °C) : 
  pforces τ (terminal.from (yob (opposite.op (⊤_ C)))) ↔ validity.is_valid τ :=
begin
  rw validity.valid_iff_section,
  split,
  { intro u, fsplit, fsplit,
    refine ⟨yob_terminal_iso_terminal.inv ≫ (pforces_to_forces _ u).lift, _⟩,
    simp only [eq_iff_true_of_subsingleton],
  },
  { intro h, 
    resetI,
    refine ⟨yob_terminal_iso_terminal.hom ≫ (section_ (canonical_incl τ)), _⟩,
    rw [assoc, is_split_epi.id, comp_id],
    exact is_terminal.hom_ext (terminal_is_terminal) _ _ }
end

-- Theorem 2.13 thesis
lemma forcing_bot : ¬ pforces ⊥ x :=
begin
  intro u,
  have i := (category_theory.yoneda_sections_small _ _).hom (pforces_to_forces _ u).lift,
  simp at i,
  have k := (external_iso_internal.bot' X).app c,
  exact pempty.elim ((presheaf.initial.pempty_obj_iso c).hom (k.inv i)),
end

lemma forcing_top : pforces ⊤ x :=
begin
  apply pforces_of_valid,
  rw validity.valid_iff_eq_sub_top,
  exact (external_iso_internal.top_sub X).symm
end

variables (σ) (τ : X ⟶ Ω °C)

lemma forcing_and : pforces (σ ⊓ τ) x ↔ pforces σ x ∧ pforces τ x :=
begin
  sorry
end

end forcing

