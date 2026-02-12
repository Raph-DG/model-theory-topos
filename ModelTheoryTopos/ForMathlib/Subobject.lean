import Mathlib.Order.Bounds.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits
import ModelTheoryTopos.ForMathlib.Skeleton

open CategoryTheory Limits

namespace CategoryTheory.Subobject

universe v u
variable {C : Type u} [Category.{v} C]

theorem prod_pullback {I : Type*} {A B : C} (f : A ⟶ B) (X : I → Subobject B)
    [HasPullbacks C] [HasProduct fun i ↦ (pullback f).obj (X i)] [HasProduct X] :
  (∏ᶜ fun i ↦ (Subobject.pullback f).obj (X i)) =
    (Subobject.pullback f).obj (∏ᶜ fun i ↦ X i) := by
  sorry

-- noncomputable def representativeIso {X : C} (A : Subobjecy X) :
--       (toThinSkeleton _).obj (representative.obj A) = A :=
--   (equivMonoOver X).counitIso.app A


theorem inf_eq_map_pullback'' [HasPullbacks C] {A : C} (f₁ : Subobject A) (f₂ : Subobject A) :
    (f₁ ⊓ f₂ : Subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) := by
  have :=  inf_eq_map_pullback' (representative.obj f₁) f₂
  convert this
  ext1
  rw [inf_def]
  congr
  apply Subobject.skeletal
  constructor
  exact (equivMonoOver A).unitIso.app f₁


theorem prod_pullback {I : Type*} {A B : C} (f : A ⟶ B) (X : I → Subobject B)
    [HasPullbacks C] [HasProduct fun i ↦ (pullback f).obj (X i)] [HasProduct X] :
  (∏ᶜ fun i ↦ (Subobject.pullback f).obj (X i)) =
    (Subobject.pullback f).obj (∏ᶜ fun i ↦ X i) := by
  sorry

instance skeletal_subobject (X : C) : Skeletal (Subobject X) := ThinSkeleton.skeletal

instance thin_subobject (X : C) : Quiver.IsThin (Subobject X) := by infer_instance

noncomputable def subobject_comp {X Y : C} (m : Subobject X) (f : X ⟶ Y) [Mono f] : Subobject Y :=
  Subobject.mk (m.arrow ≫ f)

noncomputable def underlying_obj_subobject_comp {X Y : C} (m : Subobject X) (f : X ⟶ Y) [Mono f] :
    underlying.obj (m.subobject_comp f) ≅ underlying.obj m := by
  simp [subobject_comp]
  apply underlyingIso

@[simp]
lemma subobject_equalizer {X Y : C} (f : X ⟶ Y) : equalizerSubobject f f = ⊤ := by
  apply mk_eq_top_of_isIso

end CategoryTheory.Subobject
