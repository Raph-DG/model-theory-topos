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
import ModelTheoryTopos.ForMathlib.Skeleton

open CategoryTheory Limits

namespace CategoryTheory.Subobject

universe v u
variable {C : Type u} [Category.{v} C]

@[simp]
def _root_.CategoryTheory.MonoOver.factorThru_arrow
    {X Y : C} {P : MonoOver Y} {f : X ⟶ Y} (h : MonoOver.Factors P f) :
    MonoOver.factorThru P f h ≫ P.arrow = f :=
  Classical.choose_spec h

variable {J} {B : C} (F : J → MonoOver B) [HasLimit (Discrete.functor F ⋙ (Over.isMono B).ι)]

lemma _root_.CategoryTheory.MonoOver.product_factors {A} (f : A ⟶ B) (h : ∀ i, (F i).Factors f) :
    (∏ᶜ F).Factors f :=
  have : CreatesLimit (Discrete.functor F) (Over.isMono B).ι :=
    createsLimitFullSubcategoryInclusionOfClosed _ _ _
  let := (isLimitOfPreserves (Over.isMono B).ι (productIsProduct F)).lift {
    pt := Over.mk f
    π := Discrete.natTrans fun i ↦ Over.homMk (MonoOver.factorThru _ _ (h i.as))
  }
  ⟨this.left, by simp⟩

variable (F : J → Subobject B) [i : HasLimit (Discrete.functor F ⋙ representative ⋙ (Over.isMono B).ι)]

local instance : HasProduct F :=
  have : HasLimit ((Discrete.functor F ⋙ representative) ⋙ (Over.isMono B).ι) := i
  Adjunction.hasLimit_of_comp_equivalence (Discrete.functor F) representative

lemma _root_.CategoryTheory.Subobject.product_factors {A} (f : A ⟶ B) (h : ∀ i, (F i).Factors f) :
    (∏ᶜ F).Factors f := by
  have : HasProduct (fun j ↦ representative.obj (F j)) :=
    hasLimit_of_iso (F := Discrete.functor F ⋙ representative) (eqToIso <| by ext; simp)
  rw [factors_iff, MonoOver.factors_congr _ <| PreservesProduct.iso representative F]
  have : HasLimit ((Discrete.functor fun j ↦ representative.obj (F j)) ⋙ (Over.isMono B).ι) :=
    hasLimit_of_iso (F := Discrete.functor F ⋙ representative ⋙ (Over.isMono B).ι) <|
      Functor.isoWhiskerRight (G := (Discrete.functor F ⋙ representative)) (eqToIso <| by ext; simp) (Over.isMono B).ι
  exact MonoOver.product_factors (fun j ↦ representative.obj (F j)) _ fun j ↦ (factors_iff _ _).mp <| h j
