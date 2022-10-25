import category_theory.limits.shapes.binary_products
import category_theory.limits.opposites
import category_theory.closed.cartesian

import subobject_classifier
import adjunction
import image
import topos

open category_theory category_theory.category category_theory.limits classifier


/-!
Definitions and properties of direct image of a monic
Beck-Chevalley condition

src : Sheaves, IV.3 
-/

universes v u

noncomputable theory

variables (C : Type u) [category.{v} C] [has_finite_limits C] [cartesian_closed C] [has_subobject_classifier C] [topos C]

variables {C} {c b b' : C} (k : b' ⟶ b) [mono k]

def uncurried_direct_image := classifier_of (canonical_incl ((exp.ev b').app (Ω C)) ≫ limits.prod.map k (𝟙 _))

def curried_direct_image := cartesian_closed.curry (uncurried_direct_image k)

variables {g : c ⟶ b} {k} 
lemma uncurried_beck_chevalley (s : pullback_cone g k) (is_lim : is_limit s) :
  uncurried_direct_image k ≫ (P C).map g =  