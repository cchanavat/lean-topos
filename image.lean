import category_theory.limits.shapes
import category_theory.limits.preserves.limits


import subobject_classifier
import pullbacks

/-!
# Image inside a topos

Prove that there is an image factorisation for each morphism inside a topos
TODO : prove that e is epi, will be needed for the forcing.
-/
open category_theory category_theory.category category_theory.limits classifier

noncomputable theory
universes u v
variables {C : Type u} [category.{v} C] [has_finite_limits C] [has_subobject_classifier C]

/- We need to prove some statement about the image now -/
namespace image


def monic_to_canonical_fork {X Y : C} (m : X ⟶ Y) [mono m] : 
  fork (lift_truth Y) (classifier_of m) :=
begin
  apply fork.of_ι m, rw [←assoc', terminal.comp_from m, pb_classifier_condition]
end

@[simp] lemma monic_to_canonical_fork_simp {X Y : C} (m : X ⟶ Y) [mono m] : 
  (monic_to_canonical_fork m).ι = m := by refl

/-
  In a topos, every monic is an equalizer, [SML94] pp167
-/
lemma monic_is_limit_fork {X Y : C} (m : X ⟶ Y) [mono m] : is_limit (monic_to_canonical_fork m) := 
begin
  refine fork.is_limit.mk (monic_to_canonical_fork m) _ _ _; intro s; 
  have comm : s.ι ≫ classifier_of m = terminal.from s.X ≫ truth C :=
  begin
    rw [←s.condition, ←assoc, cancel_mono], exact terminal.comp_from _ 
  end,
  { apply pb_lift_from_monic.map m s.ι comm },
  { apply pb_lift_from_monic.comm m s.ι comm },
  { apply pb_lift_from_monic.unique m s.ι comm },
end

def monic_to_fork_lift {X Y : C} (m : X ⟶ Y) [mono m]
  (f : fork (lift_truth Y) (classifier_of m)) :=
fork.is_limit.lift' (monic_is_limit_fork m) (fork.ι f) (fork.condition f)


variable [has_pushouts C]

abbreviation cokernel {X Y : C} (f : X ⟶ Y) := pushout f f
abbreviation cokernel.x {X Y : C} (f : X ⟶ Y) := (pushout.inl : Y ⟶ cokernel f)
abbreviation cokernel.y {X Y : C} (f : X ⟶ Y) := (pushout.inr : Y ⟶ cokernel f)


def canonical_factorisation {X Y : C} (f : X ⟶ Y) : mono_factorisation f := 
{ I := equalizer.{v} (cokernel.x f) (cokernel.y f),
  m := equalizer.ι (cokernel.x f) (cokernel.y f),
  e := equalizer.lift f pushout.condition }

def canonical_factorisation_condition {X Y : C} (f : X ⟶ Y) : 
  (canonical_factorisation f).m ≫ (cokernel.x f) = 
  (canonical_factorisation f).m ≫ (cokernel.y f) :=
equalizer.condition _ _

/- from [SML94] p185 -/
lemma is_image_make {X Y : C} (f : X ⟶ Y) (F' : mono_factorisation f) : 
  {l // l ≫ (monic_to_canonical_fork F'.m).ι = (canonical_factorisation f).m} :=
begin
  let s := lift_truth Y,
  let t := classifier_of F'.m,
  have h : f ≫ s = f ≫ t := by rw [←F'.fac, assoc, ←(monic_to_canonical_fork_simp F'.m),
                                    fork.condition (monic_to_canonical_fork F'.m), assoc],
  have h1 : (canonical_factorisation f).m ≫ s = (canonical_factorisation f).m ≫ t := 
  begin
    rw [←pushout.inl_desc s t h, ←assoc, canonical_factorisation_condition f], simp
  end,
  exact fork.is_limit.lift' (monic_is_limit_fork F'.m) (canonical_factorisation f).m (h1)
end
  
def is_image_canonical_factorisation {X Y : C} (f : X ⟶ Y) : 
  is_image (canonical_factorisation f) := 
{ lift := λ F', (is_image_make f F').val, 
  lift_fac' := λ F', (is_image_make f F').prop }

def image_facto {X Y : C} (f : X ⟶ Y) : image_factorisation f := 
{ F := canonical_factorisation f,
  is_image := is_image_canonical_factorisation f }

instance has_image_topos : has_images C := 
{ has_image := λ _ _ f, has_image.mk (image_facto f) }

end image