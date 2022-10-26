import category_theory.limits.shapes.finite_limits
import category_theory.subobject.basic
import category_theory.subobject.lattice


import colimits
import topos
import subobject_classifier
import pullbacks
import image

open category_theory category_theory.category category_theory.limits category_theory.limits.prod classifier 

universes v u

noncomputable theory

variables {C : Type u} [category.{v} C ]

variables [topos.{v} C] 

variables (X Y : C) (σ : X ⨯ Y ⟶ Ω C)


def π_star : subobject X ⥤ subobject (X ⨯ Y) := subobject.pullback fst

def exists' : subobject (X ⨯ Y) ⥤ subobject X := subobject.«exists» fst

-- semantics of ∃_Y σ(x, y)
local notation `Σ_` σ := classifier_of ((exists' X Y).obj (canonical_sub σ))

