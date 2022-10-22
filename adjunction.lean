import category_theory.adjunction.basic
import category_theory.types

open category_theory category_theory.category category_theory.functor category_theory.adjunction

universes v u

noncomputable theory

variables {C D : Type u} [category.{v} C] [category.{v} D] (L : C ⥤ D) (R : D ⥤ C)

/-
  Some more results about adjucntion. We promote any adjunction to a natural
  isomomorphism between hom functors, and we promote such iso to an adjunction
-/

open opposite

-- (c, d) --> C(c, Rd)
def right_hom : Cᵒᵖ × D ⥤ Type v := 
{ obj := λ x, (x.1.unop ⟶ R.obj x.2),
  map := λ _ _ f g, f.fst.unop ≫ g ≫ R.map f.snd,
  map_id' := λ x, 
    by {funext, rw [prod_id_fst, prod_id_snd, unop_id, id_comp, map_id, comp_id], refl}, 
  map_comp' := λ _ _ _ f g, by tidy }

-- (c, d) --> D(Lc, d)
def left_hom : Cᵒᵖ × D ⥤ Type v := 
{ obj := λ x, (L.obj x.1.unop ⟶ x.2),
  map := λ _ _ f g, L.map f.fst.unop ≫ g ≫ f.snd,
  map_id' := λ x, 
    by {funext, rw [prod_id_fst, prod_id_snd, unop_id, map_id, id_comp, comp_id], refl},
  map_comp' := λ _ _ _ f g, by tidy }

@[simp] lemma left_hom_obj (x : Cᵒᵖ × D) : (left_hom L).obj x = (L.obj x.1.unop ⟶ x.2) := rfl
@[simp] lemma right_hom_obj (x : Cᵒᵖ × D) : (right_hom R).obj x = (x.1.unop ⟶ R.obj x.2) := rfl

lemma left_hom_map {x y : Cᵒᵖ × D} (f : x ⟶ y) (g : (left_hom L).obj x) : 
  (left_hom L).map f g = L.map f.fst.unop ≫ g ≫ f.snd := rfl
lemma right_hom_map {x y : Cᵒᵖ × D} (f : x ⟶ y) (g : (right_hom R).obj x) : 
  (right_hom R).map f g = f.fst.unop ≫ g ≫ R.map f.snd := rfl

variables {L R}

lemma left_hom_iso_right_hom_of_adjunction (adj : L ⊣ R) : left_hom L ≅ right_hom R   :=
nat_iso.of_components 
  (λ x, (equiv.to_iso (adj.hom_equiv x.1.unop x.2) : (left_hom L).obj x ≅ (right_hom R).obj x)) 
  (begin  intros x y f,  
    ext g, simp, 
    rw [left_hom_map, map_comp, ←assoc, unit_naturality adj, map_comp, right_hom_map],
    simp only [assoc]  
   end)

def core_adjunction_of_left_hom_iso_right (i : left_hom L ≅ right_hom R) : 
  adjunction.core_hom_equiv L R :=
{ hom_equiv := λ x y, iso.to_equiv (i.app (op x, y)),
  hom_equiv_naturality_left_symm' := 
  begin
    intros c c' d f g, simp,
    convert congr_fun (i.inv.naturality ((f.op, 𝟙 d) : (op c', d) ⟶ (op c, d))) g; simp,
  end,
  hom_equiv_naturality_right' := 
  begin
    intros c d d' f g, simp,
    have g' := congr_fun (i.hom.naturality ((𝟙 (op c), g) : (op c, d) ⟶ (op c, d'))) f,
    simp at g', rw [left_hom_map, right_hom_map] at g',
    simp at g', rw [L.map_id c, id_comp (f ≫ g)] at g',
    rw g', apply id_comp,
  end }
 
def adjunction_of_left_hom_iso_right (i : left_hom L ≅ right_hom R) : L ⊣ R :=
mk_of_hom_equiv (core_adjunction_of_left_hom_iso_right i)