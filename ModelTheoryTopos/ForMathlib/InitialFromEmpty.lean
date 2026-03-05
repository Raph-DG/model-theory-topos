import Mathlib.CategoryTheory.Limits.Shapes.Terminal

noncomputable section

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

def coconeOfPointAndIsEmpty [IsEmpty C] (F : C ⥤ D) (d : D) : Cocone F where
  pt := d
  ι := {
    app X := IsEmpty.elim inferInstance X
    naturality X := IsEmpty.elim inferInstance X
  }

def natTrans_of_isEmpty [IsEmpty C] (F G : C ⥤ D) : F ⟶ G where
  app X := IsEmpty.elim inferInstance X
  naturality X := IsEmpty.elim inferInstance X

lemma hasInitial_of_hasColimit_isEmpty [h : IsEmpty C] (f : C ⥤ D) [HasColimit f] :
    HasInitial D := by
  have : ∀ (Y : D), Nonempty (colimit f ⟶ Y) := fun Y ↦
    ⟨colimit.desc f (coconeOfPointAndIsEmpty _ Y)⟩
  have : ∀ (Y : D), Subsingleton (colimit f ⟶ Y) := fun Y ↦ by
    constructor
    intro f g
    apply colimit.hom_ext
    intro J
    exact IsEmpty.elim inferInstance J
  apply hasInitial_of_unique (colimit f)

lemma hasColimit_isEmpty_of_hasInitial [h : IsEmpty C] (F : C ⥤ D) [HasInitial D] :
    HasColimit F := by
  refine ⟨coconeOfPointAndIsEmpty F (⊥_ D), ⟨fun c ↦ initial.to _, by simp, ?_⟩⟩
  intro s m h
  exact initial.hom_ext _ _

lemma hasInitial_of_hasColimitsOfShape_isEmpty [h : IsEmpty C] (k : HasColimitsOfShape C D) :
    HasInitial D := by
  apply hasInitial_of_hasColimit_isEmpty (functorOfIsEmpty C D)
