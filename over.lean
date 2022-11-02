import category_theory.limits.constructions.over
import category_theory.closed.cartesian
import category_theory.over

import topos

open category_theory category_theory.category category_theory.limits category_theory.cartesian_closed 


/-!
# Over category 

Over categories are toposes if the base is
From [MM92, IV.7] 
-/

universes v u

noncomputable theory

variables {C : Type u} [category.{v} C] [topos C]


variables {b : C}

namespace equalizer



open category_theory.over


def hom_mk' (f g : over b) (u : f.left ⟶ g.left) (comm : u ≫ g.hom = f.hom) : (f ⟶ g) := 
@over.hom_mk _ _ _ f g u (by { rw comm, apply_auto_param })

lemma hom_mk_left' {f g : over b} {u : f.left ⟶ g.left} {comm : u ≫ g.hom = f.hom} : 
  (hom_mk' f g u comm).left = u := by { unfold hom_mk', rw hom_mk_left }

-- lemma hom_mk_w' {f g : over b} {u : f ⟶ g} : u.left ≫ g.hom = f.hom := w _

variables {f g : over b} {u v : f ⟶ g}

def over_fork_of_fork (m : fork u.left v.left) : fork u v := 
fork.of_ι (hom_mk' (over.mk (m.ι ≫ f.hom)) _ m.ι (by rw mk_hom))
begin
ext, rw [comp_left, hom_mk_left', m.condition], refl
end

def over_fork_of_fork_X_hom (m : fork u.left v.left) : (over_fork_of_fork m).X.hom = m.ι ≫ f.hom :=
rfl

def over_fork_of_fork_ι_left (m : fork u.left v.left) : (over_fork_of_fork m).ι.left = m.ι :=
rfl

def fork_of_over_fork (m : fork u v) : fork u.left v.left :=
fork.of_ι m.ι.left (by { rw [←comp_left, m.condition, comp_left] })

def fork_of_over_fork_ι (m : fork u v) : (fork_of_over_fork m).ι = m.ι.left := rfl


def over_fork_lift {m : fork u.left v.left} (m_lim : is_limit m) (s : fork u v) := 
fork.is_limit.lift' m_lim (fork_of_over_fork s).ι (fork_of_over_fork s).condition


def over_fork_is_limit_of_fork_is_limit {m : fork u.left v.left} (m_lim : is_limit m) : 
  is_limit (over_fork_of_fork m) :=
begin
  apply fork.is_limit.mk _ (λ s : fork u v, hom_mk' s.X (over_fork_of_fork m).X (over_fork_lift m_lim s).val 
    begin 
    erw [over_fork_of_fork_X_hom, ←assoc, (over_fork_lift m_lim s).prop, fork_of_over_fork_ι, w], refl
    end); 
  intro s; simp only,
    ext1, erw [comp_left, (over_fork_lift m_lim s).prop], refl,
    intros t ht, ext1, apply fork.is_limit.hom_ext m_lim,
    erw fork.is_limit.lift_ι, rw [fork.ι_of_ι, fork_of_over_fork_ι, ←ht, comp_left], 
    refl
end

instance : has_limit (parallel_pair u v) :=
has_limit.mk 
  { cone := over_fork_of_fork (limit.cone (parallel_pair u.left v.left)), 
    is_limit := over_fork_is_limit_of_fork_is_limit (limit.is_limit _) }

instance : has_equalizers (over b) := has_equalizers_of_has_limit_parallel_pair (over b) 

end equalizer

instance wide_pullbacks : has_finite_wide_pullbacks C := 
has_finite_wide_pullbacks_of_has_finite_limits C

instance over_finite_limits : limits.has_finite_limits (over b) := 
category_theory.over.has_finite_limits 

