import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.RegularCategory.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import ModelTheoryTopos.ForMathlib.Subobject

open CategoryTheory Limits Regular

universe u v w

namespace CategoryTheory

section

variable (κ : Type w) (C : Type u) [Category.{v} C]

/-
This class is due to Robin Carlier. Its purpose is to allow for the `OrderBot` instance.
See https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Workaround.20.60cannot.20find.20synthesization.20order.20for.20instance.60.3F/near/573236295
Without it, the instance algorithm wouldn't be able to infer that geometric categories have `False`,
as it wouldn't know which κ we want to use.
-/
class HasFalses (C : Type u) [Category.{v} C] where
  hasInitial_subobject (X : C) : HasInitial (Subobject X)

attribute [instance] HasFalses.hasInitial_subobject

noncomputable instance {C: Type*} [Category* C] (X : C) [HasFalses C] : OrderBot (Subobject X) :=
  Preorder.orderBotOfHasInitial (C := (Subobject X))

class Geometric extends Regular C, HasFalses C where
  has_joins_subobject (X : C) (I : Set κ) : HasCoproductsOfShape I (Subobject X)
  isJoin_isStableUnderBaseChange {Y X : C} (f : Y ⟶ X) {I : Set κ} (fP : I → Subobject X) :
    ∐ (fun (i : I) ↦ (Subobject.pullback f).obj (fP i)) = (Subobject.pullback f).obj (∐ fP)

attribute [instance] Geometric.has_joins_subobject
attribute [simp] Geometric.isJoin_isStableUnderBaseChange

abbrev Coherent := Geometric C Bool

end

namespace Geometric

variable {κ : Type w} {C : Type u} [Category.{v} C]
variable [geo : Geometric κ C]

lemma emptyJoin_eq_bot (X : C) : ∐ (fun (i : (∅ : Set κ)) ↦ by aesop) = (⊥ : Subobject X) := by
  apply le_bot_iff.mp
  apply leOfHom
  apply Limits.Sigma.desc
  grind

@[simp]
lemma bot_isStableUnderBaseChange {Y X : C} (f : Y ⟶ X) :
    (Subobject.pullback f).obj ⊥ = ⊥ := by
  rw [← emptyJoin_eq_bot (κ := κ), ← emptyJoin_eq_bot (κ := κ), ← isJoin_isStableUnderBaseChange]
  rw [emptyJoin_eq_bot (κ := κ)]
  apply le_bot_iff.mp
  apply leOfHom
  apply Limits.Sigma.desc
  grind

lemma inf_join_eq_join_inf {X : C} {I : Set κ} (P : Subobject X) (Qᵢ : I → Subobject X) :
    (P ⨯ ∐ Qᵢ) = ∐ (fun i ↦ P ⨯ Qᵢ i) := by
  rw [Subobject.prod_eq_inf, Subobject.inf_eq_map_pullback'', ← Geometric.isJoin_isStableUnderBaseChange]
  have := Subobject.mapPullbackAdj P.arrow
  have : (Subobject.map P.arrow).obj (∐ fun i ↦ (Subobject.pullback P.arrow).obj (Qᵢ i)) =
     (∐ fun i ↦ (Subobject.map P.arrow).obj <| (Subobject.pullback P.arrow).obj (Qᵢ i)) := by
    apply Subobject.skeletal
    constructor
    have := (Subobject.mapPullbackAdj P.arrow).isLeftAdjoint
    apply PreservesCoproduct.iso
  rw [this]
  congr
  funext
  rw [← Subobject.inf_eq_map_pullback'', Subobject.prod_eq_inf]

end Geometric

section goodFrobenius

namespace Regular
open Subobject

variable {C : Type u} [Category.{v} C] [Regular C]

/- Sanity check. -/
example (X : C) : HasFiniteProducts (Subobject X) := inferInstance

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (h : IsPullback fst snd f g) (A : Subobject Y)

/--
     snd* A ------frob-------▷ f* ∃g(A)
        /|                     /|
       / |                    / |
      /  |                   /  |
     V   |                  V   |
    P ---------fst-------> X    |
    |    |                 |    |
    |    V                 |    V
    |    A ----------------|-▷ ∃g(A)
  snd   /                  f   /
    |  /                   |  /
    | /                    | /
    VV                     VV
    Y ----------g--------> B
-/
noncomputable def frobeniusMorphism' :
  underlying.obj ((Subobject.pullback snd).obj A) ⟶
    underlying.obj ((Subobject.pullback f).obj ((«exists» g).obj A)) :=
  (Subobject.isPullback f ((«exists» g).obj A)).lift
    (Subobject.pullbackπ snd A ≫ (Subobject.imageFactorisation g A).F.e)
    (((Subobject.pullback snd).obj A).arrow ≫ fst)
    (by simp [h.w, ← imageFactorisation_F_m, ← (Subobject.isPullback snd _).w_assoc,
      (Subobject.imageFactorisation g A).F.fac])

lemma frobeniusMorphism'IsPullback :
  IsPullback (frobeniusMorphism' h A) (Subobject.pullbackπ snd A)
    (Subobject.pullbackπ f ((«exists» g).obj A)) (Subobject.imageFactorisation g A).F.e := by
  apply IsPullback.of_right (t := (Subobject.isPullback f ((«exists» g).obj A)).flip)
    (p := by simp [frobeniusMorphism'])
  simp [frobeniusMorphism', ← imageFactorisation_F_m]
  apply (Subobject.isPullback snd A).flip.paste_horiz
  exact h

instance : IsRegularEpi (frobeniusMorphism' h A) := by
  apply regularEpiIsStableUnderBaseChange.of_isPullback (frobeniusMorphism'IsPullback h A).flip
  simp only [MorphismProperty.regularEpi_iff]
  have := strongEpi_of_strongEpiMonoFactorisation (strongEpiMonoFactorisation (A.arrow ≫ g))
    (imageFactorisation g A).isImage
  infer_instance

@[simps!]
noncomputable def frobeniusStrongEpiMonoFactorisation' :
    StrongEpiMonoFactorisation <| ((Subobject.pullback snd).obj A).arrow ≫ fst where
  I := underlying.obj ((Subobject.pullback f).obj ((«exists» g).obj A))
  m := ((Subobject.pullback f).obj ((«exists» g).obj A)).arrow
  e := frobeniusMorphism' h A
  fac := by simp [frobeniusMorphism']

include h in
theorem frobenius_reciprocity :
    («exists» fst).obj ((Subobject.pullback snd).obj A) =
      (Subobject.pullback f).obj ((«exists» g).obj A) :=
  eq_of_comm
    (IsImage.isoExt (imageFactorisation _ _).isImage
      (frobeniusStrongEpiMonoFactorisation' h A).toMonoIsImage)
    (IsImage.isoExt_hom_m (imageFactorisation _ _).isImage
      (frobeniusStrongEpiMonoFactorisation' h A).toMonoIsImage)

end Regular
end goodFrobenius
