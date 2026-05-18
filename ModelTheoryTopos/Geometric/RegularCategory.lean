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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Closed.Monoidal
import ModelTheoryTopos.ForMathlib.Subobject
import ModelTheoryTopos.ForMathlib.InitialFromEmpty

open CategoryTheory Limits Regular

universe u v w r

namespace CategoryTheory

section

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

class Geometric (κ : Cardinal.{w}) [κ_isRegular : Fact κ.IsRegular] (C : Type u) [Category.{v} C]
    extends Regular C, HasFalses C where
  has_joins_subobject (X : C) (I : Type w) [Fact <| HasCardinalLT I κ] :
    HasCoproductsOfShape I (Subobject X)
  isJoin_isStableUnderBaseChange {Y X : C} (f : Y ⟶ X) {I : Type w}
    [Fact <| HasCardinalLT I κ] (fP : I → Subobject X) :
    ∐ (fun (i : I) ↦ (Subobject.pullback f).obj (fP i)) = (Subobject.pullback f).obj (∐ fP)

attribute [instance] Geometric.has_joins_subobject
attribute [simp] Geometric.isJoin_isStableUnderBaseChange

abbrev Coherent.{k} (C : Type u) [Category.{v} C] : Prop :=
  Geometric (κ_isRegular := ⟨Cardinal.isRegular_aleph0⟩) Cardinal.aleph0.{k} C

end

namespace Geometric

variable {κ : Cardinal.{w}} [κ_isRegular : Fact κ.IsRegular] {C : Type u} [Category.{v} C]
variable [geo : Geometric κ C]

local instance foo (I : Type w) [IsEmpty I] : Fact <| HasCardinalLT I κ :=
  ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le κ_isRegular.out)⟩

include geo in
lemma foo' (I : Type w) [IsEmpty I] (X : C) (f : I → Subobject X) : HasCoproduct f := by
  apply hasColimit_isEmpty_of_hasInitial

lemma emptyJoin_eq_bot' (X : C) (I : Type*) [IsEmpty I] (f : I → Subobject X) [h : HasCoproduct f] :
  ∐ f = (⊥ : Subobject X) := by
  apply le_bot_iff.mp
  apply leOfHom
  apply Limits.Sigma.desc
  intro b
  exact IsEmpty.elim inferInstance b

def myfunc (X : C) : PEmpty.{k} → Subobject X := PEmpty.elim

noncomputable def test (X : C) : Subobject X := ∐ (myfunc.{u,v,w+1} X)

lemma emptyJoin_eq_bot (X : C) :
    ∐ (myfunc.{u,v,w + 1} X) = (⊥ : Subobject X) := by
  apply le_bot_iff.mp
  apply leOfHom
  apply Limits.Sigma.desc
  intro b
  exact IsEmpty.elim inferInstance b

-- set_option pp.universes true
@[simp]
lemma bot_isStableUnderBaseChange {Y X : C} (f : Y ⟶ X) :
    (Subobject.pullback f).obj ⊥ = ⊥ := by
  rw [← emptyJoin_eq_bot (κ := κ), ← emptyJoin_eq_bot (κ := κ)]
  have := isJoin_isStableUnderBaseChange f (myfunc X) (κ := κ)
  rw [← this]
  rw [emptyJoin_eq_bot (κ := κ)]
  apply le_bot_iff.mp
  apply leOfHom
  apply Limits.Sigma.desc
  intro b
  exact IsEmpty.elim inferInstance b

lemma inf_join_eq_join_inf {X : C} (I : Type w) [Fact <| HasCardinalLT I κ] (P : Subobject X) (Qᵢ : I → Subobject X) :
    (P ⨯ ∐ Qᵢ) = ∐ (fun i ↦ P ⨯ Qᵢ i) := by
  rw [Subobject.prod_eq_inf, Subobject.inf_eq_map_pullback'', ← geo.isJoin_isStableUnderBaseChange]
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

variable {C : Type*} [Category* C] [HasPullbacks C] {X Y : C}

abbrev HasForall (f : X ⟶ Y) := (Subobject.pullback f).IsLeftAdjoint

variable (f : X ⟶ Y) [h : HasForall f]

noncomputable def «forall» := (Subobject.pullback f).rightAdjoint

variable (C)
abbrev HasForalls := ∀ {X Y : C} (f : X ⟶ Y), HasForall f

noncomputable instance [HasPullbacks C] (X : C) : CartesianMonoidalCategory (Subobject X) :=
    CartesianMonoidalCategory.ofChosenFiniteProducts (C := Subobject X)
      ⟨asEmptyCone ⊤, Preorder.isTerminalTop _⟩
      (fun A B ↦ ⟨BinaryFan.mk (homOfLE inf_le_left) (homOfLE inf_le_right),
        Preorder.isLimitBinaryFan A B⟩)

abbrev HasImplies := ∀ X : C, MonoidalClosed <| Subobject X
