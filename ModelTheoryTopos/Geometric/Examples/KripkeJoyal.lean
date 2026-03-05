import ModelTheoryTopos.Geometric.Structure
import Mathlib

open CategoryTheory Limits Signature

/-

# Kripke-Joyal semantics.

We recall Kripke-Joyal semantics, as described in section VI.6 of _Sheaves in Geometry and Logic_.
Let, `α : U ⟶ X` be a generalized element of `X`, i.e. just a morphism to `X`, and `φ` be a
proposition on `X`, i.e. just a subobject of `X`.
The interpretation of the forcing relation `U ⊩ φ(α)` ("U forces φ") is a morphism `s : U ⟶ φ`, such
that `s ≫ φ = α`.

This can be interpreted into our system, at least when `α` is a mono. Indeed, then it induces a
subobject, which we could interpret as part of our `FormulaContext`. This file does precisely that.
-/

universe w v u

section
namespace Signature

variable (S : Signature)

def ExtendOneSymbol : Signature :=
  (S.extendSorts Option.some).extendSymbols (Unit) (fun _ ↦ .inj none)

variable (κ : Cardinal.{w}) [Fact <| Cardinal.IsRegular κ]
variable {C : Type u} [Category.{v} C] [Geometric κ C] (M : Structure S C)
variable (X' : C) (U' : C) (f : U' ⟶ X') [Mono f]

def StructureExtend : Structure S.ExtendOneSymbol C where
  sorts X := match X with
  | .some X => ⟦M|X⟧ˢ
  | .none => X'
  Functions f := M.Functions f
  Relations := sorry

-- Extend interpretations to an interpretation of ExtendOneSymbol
