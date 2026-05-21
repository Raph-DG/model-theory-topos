import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

open CategoryTheory Limits

namespace Signature

inductive DerivedSorts (Sorts : Type*) where
  | inj : Sorts → DerivedSorts Sorts
  | prod {n : ℕ} : (Fin n → DerivedSorts Sorts) → DerivedSorts Sorts

/-- The functorial action of `DerivedSorts`. -/
def DerivedSorts.map {X Y : Type*} (f : X → Y) :
  DerivedSorts X → DerivedSorts Y
  | .inj x => .inj <| f x
  | .prod xᵢ => .prod <| fun i ↦ .map f (xᵢ i)

instance : Functor DerivedSorts where
  map := .map

instance {Sorts : Type*} : Coe Sorts (DerivedSorts Sorts) where
  coe A := DerivedSorts.inj A

structure SortedSymbols (Sorts : Type*) where
  Symbols : Type*
  domain : Symbols → DerivedSorts Sorts

attribute [coe] SortedSymbols.Symbols

instance {Sorts : Type*} : CoeSort (SortedSymbols Sorts) Type* where
  coe := SortedSymbols.Symbols

abbrev SortedSymbols.Symbols.domain
  {Sorts : Type*} {X : SortedSymbols Sorts} (x : X) := X.domain x

structure SortedSymbolsWOutput (Sorts : Type*) extends SortedSymbols Sorts where
  codomain : Symbols → DerivedSorts Sorts

/-- The functorial action of `SortedSymbols`. -/
def SortedSymbolsWOutput.map {X Y : Type*} (f : X → Y) :
  SortedSymbolsWOutput X → SortedSymbolsWOutput Y := fun S ↦ {
    Symbols := S.Symbols
    domain x := DerivedSorts.map f (S.domain x)
    codomain x := DerivedSorts.map f (S.codomain x)
  }

attribute [coe] SortedSymbolsWOutput

instance {Sorts} : CoeSort (SortedSymbolsWOutput Sorts) Type* where
  coe X := X.toSortedSymbols

abbrev SortedSymbols.Symbols.codomain
  {Sorts : Type*} {X : SortedSymbolsWOutput Sorts} (x : X) :
  DerivedSorts Sorts := X.codomain x

end Signature

structure Signature where
  Sorts : Type*
  Functions : Signature.SortedSymbolsWOutput Sorts
  Relations : Signature.SortedSymbols Sorts

instance : CoeSort Signature Type* where
  coe S := Signature.DerivedSorts S.Sorts

def Signature.extendSorts {S' : Type} (S : Signature) (f : S.Sorts → S') : Signature where
  Sorts := S'
  Functions := SortedSymbolsWOutput.map f S.Functions
  Relations := SortedSymbols.map f S.Relations

def Signature.extendSymbols (S : Signature) (X : Type*) (h : X → DerivedSorts S.Sorts) : Signature where
  Sorts := S.Sorts
  Functions := S.Functions
  Relations := {
    Symbols := S.Relations ⊕ X
    domain f :=
      match f with
      | .inl a => S.Relations.domain a
      | .inr x => h x
  }
