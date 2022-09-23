import category_theory.limits.types
import category_theory.functor
import category_theory.limits.shapes.functor_category

open category_theory category_theory.limits functor


universes v u
noncomputable theory
variables (C : Type u) [category.{u} C] [small_category C] [has_limits C]


-- set_option trace.class_instances true


def one_map_Type {X Y : Type u} (m : X ⟶ Y) : cone (cospan m m) :=
  limit.cone (cospan m m) 

def two_maps_Type {X Y : Type u} (m m' : X ⟶ Y) : cone (cospan m m') :=
  limit.cone (cospan m m') 

-- A workaround
def Types_inst := category_theory.types.{u}

def one_map_Type' {X Y : Type u} (m : X ⟶ Y) : cone (cospan m m) :=
  @limit.cone _ _ _ Types_inst.{u} (cospan m m) _

-- A non-workaround
def one_map_Type'' {X Y : Type u} (m : X ⟶ Y) : cone (cospan m m) :=
  @limit.cone _ _ _ category_theory.types.{u} (cospan m m) _

