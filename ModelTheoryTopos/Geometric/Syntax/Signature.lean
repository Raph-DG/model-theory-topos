import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Signatures

In this file, we define (multisorted, finitary, non-dependent) signatures. These consist of a type
of sorts, a type of function symbols and a type of relation symbols.
-/

namespace Signature

/--
The type of derived sorts, i.e. those that are tuples (or tuples of tuples, etc.) of the original
type of sorts.

Implementation note: We use this presentation, instead of, say, just considering `Fin n → Sorts`
because this way it's easier to pair terms. See `Term.pair`.
-/
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

/--
An element of `SortedSymbols Sorts` is a type of symbols and a choice of a derived sort for each
symbol.
-/
structure SortedSymbols (Sorts : Type*) where
  Symbols : Type*
  domain : Symbols → DerivedSorts Sorts

attribute [coe] SortedSymbols.Symbols

instance {Sorts : Type*} : CoeSort (SortedSymbols Sorts) Type* where
  coe := SortedSymbols.Symbols

/-- The functorial action of `SortedSymbols`. -/
def SortedSymbols.map {X Y : Type*} (f : X → Y) :
  SortedSymbols X → SortedSymbols Y := fun S ↦ {
    Symbols := S.Symbols
    domain x := DerivedSorts.map f (S.domain x)
  }

/-- Extends The functorial action of `SortedSymbols`. -/
def SortedSymbols.extendOnce {X : Type*} (S : SortedSymbols X) (s : DerivedSorts X) :
  SortedSymbols X := {
    Symbols := WithTop S.Symbols
    domain x := WithTop.recTopCoe s S.domain x
  }

/-- The domain of a sorted symbol. -/
abbrev SortedSymbols.Symbols.domain
  {Sorts : Type*} {X : SortedSymbols Sorts} (x : X) := X.domain x

/--
A type of sorted symbols with output contains the data of a `SortedSymbol` but also specifies a
codomain for each symbol.
-/
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

/-- The codomain of a sorted symbol. -/
abbrev SortedSymbols.Symbols.codomain
  {Sorts : Type*} {X : SortedSymbolsWOutput Sorts} (x : X) :
  DerivedSorts Sorts := X.codomain x

end Signature

/-- A signature consists of sorts, function symbols (with output) and relation symbols. -/
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
