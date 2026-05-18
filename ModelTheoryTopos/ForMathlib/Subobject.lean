import Mathlib.Order.Bounds.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.RegularCategory.Basic
import ModelTheoryTopos.ForMathlib.ProductSubobject

open CategoryTheory Limits

namespace CategoryTheory.Subobject

universe v u
variable {C : Type u} [Category.{v} C]

noncomputable def toThinSkeleton_eq {X : C} (A : Subobject X) :
    (toThinSkeleton _).obj (representative.obj A) = A :=
  Subobject.skeletal _ ⟨((equivMonoOver X).unitIso.app _).symm⟩

theorem inf_eq_map_pullback'' [HasPullbacks C] {A : C} (f₁ : Subobject A) (f₂ : Subobject A) :
    (f₁ ⊓ f₂ : Subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) := by
  convert inf_eq_map_pullback' (representative.obj f₁) f₂
  ext1
  nth_rw 1 [← toThinSkeleton_eq f₁]
  congr

noncomputable def underlyingIsoMap' {A X Y : C} (f : X ⟶ Y) [Mono f] (A' : A ⟶ X) [Mono A'] :
    underlying.obj ((Subobject.map f).obj (Subobject.mk A')) ≅ A := by
  simp [map, lower, mk, ThinSkeleton.mk, Quotient.mk']
  exact underlyingIso ((MonoOver.map f).obj (MonoOver.mk A')).arrow

theorem prod_pullback {n : ℕ} {A B : C} (f : A ⟶ B) (X : Fin n → Subobject B) [HasFiniteLimits C] :
  (∏ᶜ fun i ↦ (Subobject.pullback f).obj (X i)) =
    (Subobject.pullback f).obj (∏ᶜ fun i ↦ X i) := by
  refine Subobject.skeletal _ ⟨?_⟩
  let mycone : Cone (Discrete.functor fun i ↦ (pullback f).obj (X i)) := {
    pt := (Subobject.pullback f).obj (∏ᶜ fun i ↦ X i)
    π := ⟨fun i ↦ (pullback f).map <| Pi.π _ i.as, by cat_disch⟩
  }
  have : IsLimit mycone := {
    lift s := by
      apply homOfFactors
      simp [mycone]
      apply pullback_factors
      apply product_factors
      intro i
      rw [factors_iff]
      refine ⟨underlying.map (s.π.app ⟨i⟩) ≫ pullbackπ f _, ?_⟩
      simp [(isPullback f _).w]
  }
  simpa using IsLimit.conePointUniqueUpToIso (productIsProduct _) this

instance skeletal_subobject (X : C) : Skeletal (Subobject X) := ThinSkeleton.skeletal

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
