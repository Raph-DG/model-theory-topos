import ModelTheoryTopos.Geometric.Structure
import Mathlib

open CategoryTheory Limits Signature Sheaf

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (κ : Cardinal.{w}) [Fact <| Cardinal.IsRegular κ]

-- instance foo [HasFiniteColimits C] : HasCoequalizers C where

instance regular_of_sheaf : Regular (Sheaf J (Type max u v)) where
  hasCoequalizer_of_isKernelPair _ := inferInstance
  regularEpiIsStableUnderBaseChange := by
    sorry

instance geometric_of_sheaf :
    Geometric κ (Sheaf J (Type max u v)) where
  hasInitial_subobject X := sorry
  has_joins_subobject X I := by
    -- See Sheaves in Geometry and logic III.8
    sorry
  isJoin_isStableUnderBaseChange := sorry

variable {S : Signature} (M : Structure S (Sheaf J (Type max u v)))

def is_true {xs : Context S} (φ : xs ⊢ᶠ𝐏) : Prop := ⟦M|φ⟧ᶠ = ⊤

-- Make the usual translation of kripe-joyal into sheaves
-- E.g. The semantics of U forces ∀ x, φ(x) should be translated into a usable thing

-- Define formula_at_stalk : Formula -> Prop. Given some formula φ on context X, this is just the
-- stalk of φ at a point.

-- Show that formula_at_stalk commutes with all type formers.

-- Then do Ingo's arguments.


open TopCat


-- variable (M : Structure RingSignature (Sheaf Type X))

-- def sheafOfRingsOfInternalRing (h : Theory.interpret M RingTheory) : Sheaf CommRingCat X where
--   val := {
--     obj X :=
--       have : CommRing ((M.sorts ()).val.obj X) := sorry
--       .of ((M.sorts ()).val.obj X)
--     map := sorry
--   }
--   cond := sorry

-- def structureOfSheafOfRings (s : Sheaf CommRingCat X) :
--     Structure RingSignature (Sheaf Type X) where
--   sorts x := sorry
--   Functions := sorry
--   Relations r := by cases r

-- def internalRingOfSheafOfRings (s : Sheaf CommRingCat X) :
--     Theory.interpret (structureOfSheafOfRings s) RingTheory :=
--   sorry
