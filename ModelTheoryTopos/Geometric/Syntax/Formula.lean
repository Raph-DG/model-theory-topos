import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import ModelTheoryTopos.Geometric.Syntax.Term
import ModelTheoryTopos.ForMathlib.Data.Fin.VecNotation

/-!
# Formulas and friends

In this file, we define provide the following definitions:
- `Formula`: This type consists of the well-formed geometric formulas relative to a signature. These
  consist of relations, true, false, binary conjugation, infinitary disjuction (of a certain size),
  equalities and existentials.
- `FormulaContext`: This type consists of vectors of formulas.
- `Sequent`: A sequent is a pair of formulas (the premise and the conclusion) on a same context.
- `Theory`: This is a set of sequents.

We additionally provide basic API and results about these, e.g. that we can substitute formulas
along context morphisms.

## Implementation detail
The infinitary conjunction are all relative to a certain cardinal. We define the class
`SmallUniverse` to keep around a type over which we are indexing our infinitary disjunctions.

-/

namespace Signature

open Cardinal CategoryTheory

variable {S : Signature}

/-- Inductive definition of a formula over a context. -/
inductive Formula (κ : Cardinal.{w}) [κ_isRegular : Fact κ.IsRegular] : S.Context → Type _ where
  | rel {xs} (R : S.Relations) : Term xs (R.domain) → Formula κ xs
  | true {xs} : Formula κ xs
  | false {xs} : Formula κ xs
  | conj {xs} : Formula κ xs → Formula κ xs → Formula κ xs
  | infdisj {xs} {I : Type w} [Fact <| HasCardinalLT I κ] : (I → Formula κ xs) → Formula κ xs
  | eq {xs A} : ⊢ᵗ[xs] A → ⊢ᵗ[xs] A → Formula κ xs
  | exists {A xs} : Formula κ (A ∶ xs) → Formula κ xs

scoped notation:max "⊤'" => Formula.true
scoped notation:max "⊥'" => Formula.false
scoped infixr:62 " ∧' " => Formula.conj
scoped prefix:100 "⋁'" => Formula.infdisj
scoped infixr:50 " =' " => Formula.eq
scoped prefix:110 "∃'" => Formula.exists


scoped syntax:25 term:51 " ⊢ᶠ𝐏" : term
scoped macro_rules
  | `($xs ⊢ᶠ𝐏) => `(Formula $(Lean.mkIdent `κ) $xs) -- Hack to not reference κ

variable {κ : Cardinal.{w}} [κ_isRegular : Fact κ.IsRegular]

/-- Substitution of a formula along a context morphism. -/
@[reducible]
def Formula.subst {ys xs : S.Context} (σ : ys ⟶ xs) (φ : xs ⊢ᶠ𝐏) : ys ⊢ᶠ𝐏 :=
  match φ with
  | rel R t => .rel R (t.subst σ)
  | ⊤' => ⊤'
  | ⊥' => ⊥'
  | φ ∧' Q => (φ.subst σ) ∧' (Q.subst σ)
  | ⋁' φᵢ => ⋁' (fun i ↦ (φᵢ i).subst σ)
  | t1 =' t2 => (t1.subst σ) =' (t2.subst σ)
  | .exists (A := A) φ => ∃' (φ.subst ((Context.consFunctor A).map σ))

@[simp]
lemma Formula.subst_id {xs : S.Context} (φ : xs ⊢ᶠ𝐏) :
    φ.subst (𝟙 xs) = φ := by
  induction φ with
  | rel _ _ => simp
  | true => simp
  | false => simp
  | conj _ _ h h' => simp [h, h']
  | infdisj _ h => simp [h]
  | eq _ _ => simp
  | @«exists» A zs φ h => simpa using h

lemma Formula.subst_comp {zs : S.Context} (φ : zs ⊢ᶠ𝐏) :
    {xs ys : S.Context} → (σ : xs ⟶ ys) → (σ' : ys ⟶ zs) →
    φ.subst (σ ≫ σ') = (φ.subst σ').subst σ := by
  induction φ with
  | rel _ _ => simp [Term.subst_comp]
  | true => simp
  | false => simp
  | conj _ _ h h' => simp [h, h']
  | infdisj _ h => simp [h]
  | eq _ _ => simp [Term.subst_comp]
  | @«exists» A zs φ h => simp; intro xs ys σ σ'; rw [← h]

variable (κ) in
/-- A `FormulaContext` is a vector of formulas. -/
@[ext]
structure FormulaContext (xs : S.Context) where
  length : ℕ
  nth : Fin length → Formula κ xs

/-- The empty formula context. -/
def FormulaContext.nil (xs : S.Context) : FormulaContext κ xs where
  length := 0
  nth := ![]

variable {ys xs : S.Context} (Γ : FormulaContext κ xs)

@[simp]
lemma FormulaContext.length_0_isNil (φ : Fin 0 → Formula κ xs) :
    FormulaContext.mk 0 φ = FormulaContext.nil xs := by
  ext <;> simp [nil]; ext i; exact Fin.elim0 i

/-- Extending a formula context with a new formula. -/
@[reducible]
def FormulaContext.cons (φ : Formula κ xs) : FormulaContext κ xs where
  length := Γ.length + 1
  nth := Matrix.vecCons φ Γ.nth

@[simp]
lemma FormulaContext.cons_nth0 (Γ : FormulaContext κ xs) (φ) : (Γ.cons φ).nth 0 = φ := by simp

@[simp]
lemma FormulaContext.lenght_cons (φ : Formula κ xs) : (Γ.cons φ).length = Γ.length + 1 := by
  simp

/-- Extending a formula context with a new formula, by `snoc`-ing it. -/
def FormulaContext.snoc (φ : Formula κ xs) : FormulaContext κ xs where
  length := Γ.length + 1
  nth := Matrix.vecSnoc φ Γ.nth

/-- Substitution of a formula context along a context morphism. -/
def FormulaContext.subst (Γ : FormulaContext κ xs) (σ : ys ⟶ xs) : FormulaContext κ ys where
  length := Γ.length
  nth i := (Γ.nth i).subst σ

@[simp]
lemma FormulaContext.subst_id (Γ : FormulaContext κ xs) : Γ.subst (𝟙 xs) = Γ := by
  ext <;> simp [subst]

lemma FormulaContext.subst_nth (σ : ys ⟶ xs) (Γ : FormulaContext κ xs) (i) :
    (Γ.subst σ).nth i = (Γ.nth i).subst σ := by
  simp [subst]

lemma FormulaContext.subst_cons (σ : ys ⟶ xs) (Γ : FormulaContext κ xs) (φ : Formula κ xs) :
    (Γ.cons φ).subst σ = (Γ.subst σ).cons (φ.subst σ) := by
  ext
  · simp [subst]
  · simp only [subst, heq_eq_eq]; funext i; cases i using Fin.cases <;> simp

lemma FormulaContext.subst_comp {zs} (σ' : zs ⟶ ys) (σ : ys ⟶ xs) (Γ : FormulaContext κ xs) :
    Γ.subst (σ' ≫ σ) = (Γ.subst σ).subst σ' := by
  ext
  · simp [subst]
  · simp only [subst, heq_eq_eq]; funext; simp [Formula.subst_comp]

instance instHAppendFormulaContext :
    HAppend (FormulaContext κ xs) (FormulaContext κ xs) (FormulaContext (κ := κ) xs) where
  hAppend Δ Γ := {
    length := Δ.length + Γ.length
    nth := Matrix.vecAppend (by simp) Δ.nth Γ.nth
  }

section

variable (Δ Γ : FormulaContext κ xs)

@[simp]
lemma FormulaContext.append_length : (Δ ++ Γ).length = Δ.length + Γ.length := by
  rfl

@[simp]
lemma FormulaContext.append_nth_l'' (i : ℕ) (k : i < Δ.length) (l : i < (Δ ++ Γ).length) :
    (Δ ++ Γ).nth ⟨i, l⟩ = Δ.nth ⟨i, k⟩ := by
  simp [HAppend.hAppend, Matrix.vecAppend_eq_ite]; aesop

@[simp]
lemma FormulaContext.append_nth_l' (i : Fin Δ.length) (l : i < (Δ ++ Γ).length) :
    (Δ ++ Γ).nth ⟨i, l⟩ = Δ.nth i := by
  simp [HAppend.hAppend, Matrix.vecAppend_eq_ite]

@[simp]
lemma FormulaContext.append_nth_l (i : Fin Δ.length) :
    (Δ ++ Γ).nth ⟨i, by simp; omega⟩ = Δ.nth i := by
  simp [HAppend.hAppend, Matrix.vecAppend_eq_ite]

@[simp]
lemma FormulaContext.append_nth_r''
    (i : ℕ) (k : i < Γ.length) (l : Δ.length + i < (Δ ++ Γ).length) :
    (Δ ++ Γ).nth ⟨Δ.length + i, l⟩ = Γ.nth ⟨i, k⟩ := by
  simp [HAppend.hAppend, Matrix.vecAppend_eq_ite]

@[simp]
lemma FormulaContext.append_nth_r' (i : Fin Γ.length) (l : Δ.length + ↑i < (Δ ++ Γ).length) :
    (Δ ++ Γ).nth ⟨Δ.length + i, l⟩ = Γ.nth i := by
  simp [HAppend.hAppend, Matrix.vecAppend_eq_ite]

@[simp]
lemma FormulaContext.append_nth_r (i : Fin Γ.length) :
    (Δ ++ Γ).nth ⟨Δ.length + i, by simp⟩ = Γ.nth i := by
  simp [HAppend.hAppend, Matrix.vecAppend_eq_ite]

lemma FormulaContext.subst_append (σ: ys ⟶ xs) :
    (Δ ++ Γ).subst σ = Δ.subst σ ++ Γ.subst σ := by
  ext
  · rfl
  · apply heq_of_eq
    funext ⟨i, k⟩;
    by_cases h : i < Δ.length
    · rw [FormulaContext.append_nth_l'' (Δ.subst σ) (Γ.subst σ) i h k]
      simp [subst]
      rw [FormulaContext.append_nth_l'' Δ Γ i]
    · let j := i - Δ.length
      have i_eq : i = Δ.length + j:= by omega
      have fin_eq : Fin.mk i k = ⟨Δ.length + j, by rw [← i_eq]; exact k⟩ := by grind
      rw [fin_eq]
      simp [subst] at k
      have p := FormulaContext.append_nth_r'' (Δ.subst σ) (Γ.subst σ) j (by simp [subst]; omega) (by simp [subst]; omega)
      simp [subst] at *
      rw [p, FormulaContext.append_nth_r'' Δ Γ j]

/--
We say that a formula `φ` is a member of a formula context `Γ` if there is a witness `i` such that
the `i`th formula in `Γ` is `φ`.
-/
def FormulaContext.mem (φ : Formula κ xs) (Γ : FormulaContext (κ := κ) xs) : Type _ :=
  {i // Γ.nth i = φ}

scoped infixr:62 " ∈' " => FormulaContext.mem

/--
If a formula is a formula context, then it is also in that same formul context extended with a new
formula.
-/
def FormulaContext.mem_cons {Γ : FormulaContext (κ := κ) xs} {ψ : Formula κ xs} (ψinΓ : ψ ∈' Γ) (φ) :
  ψ ∈' Γ.cons φ := ⟨ψinΓ.1.succ, ψinΓ.2⟩

/--
We say that a formula context `Δ` is included in `Γ` iff all the formulas in `Δ` are also in `Γ`.
-/
def FormulaContext.incl (Δ Γ : FormulaContext (κ := κ) xs) :=
  ∀ ψ, ψ ∈' Δ → ψ ∈' Γ

scoped infixr:62 " ⊆' " => FormulaContext.incl

/-- A formula context is included in its own extension. -/
def FormulaContext.incl_cons (Γ : FormulaContext (κ := κ) xs) (ψ : Formula κ xs) :
  Γ ⊆' (Γ.cons ψ) := fun _ ⟨i, p⟩ ↦ ⟨i.succ, p⟩

/-- Inclusion of formula contexts is preserved under substitution. -/
def FormulaContext.incl_subst {Δ Γ : FormulaContext (κ := κ) xs} (ξ : Δ ⊆' Γ) (σ : ys ⟶ xs) :
    Δ.subst σ ⊆' Γ.subst σ := fun ψ ⟨i, p⟩ ↦
  let ⟨j, k⟩ := ξ (Δ.nth i) ⟨i, rfl⟩
  ⟨j, by rw [FormulaContext.subst_nth, k, ← FormulaContext.subst_nth, p]⟩

/-- Inclusion of formula contexts is preserved under formula context extension. -/
def FormulaContext.incl_cons_cons {Δ Γ : FormulaContext (κ := κ) xs} (φ) (ξ : Δ ⊆' Γ) :
    Δ.cons φ ⊆' Γ.cons φ := fun ψ ⟨i, p⟩ ↦
  Fin.cases (motive := fun j ↦ (Δ.cons φ).nth j = ψ → ψ ∈' Γ.cons φ)
    (fun p ↦ p ▸ ⟨0, rfl⟩)
    (fun i p ↦ p ▸ FormulaContext.mem_cons (ξ (Δ.nth i) ⟨i, rfl⟩) φ)
    i p

/-- If `Γ' ++ Γ ⊆' Δ` then `Γ ⊆' Δ`. -/
def FormulaContext.append_incl_l {Δ Γ Γ' : FormulaContext (κ := κ) xs} :
  Γ' ++ Γ ⊆' Δ → Γ ⊆' Δ :=
  fun ξ φ ⟨⟨i, leq⟩, p⟩ ↦
    ξ φ ⟨⟨Γ'.length + i, by simp [leq]⟩, by rw [FormulaContext.append_nth_r' (i := ⟨i, leq⟩), p]⟩

instance instMembershipFormulaContext : Membership (Formula κ xs) (FormulaContext (κ := κ) xs) where
  mem Γ φ := ∃ i, Γ.nth i = φ

@[simp]
lemma FormulaContext.append_nil : Γ ++ FormulaContext.nil (κ := κ) xs = Γ := by
  ext <;> simp [nil, HAppend.hAppend]

@[simp]
lemma FormulaContext.nil_append : FormulaContext.nil (κ := κ) xs ++ Γ = Γ := by
  ext
  · simp [nil, HAppend.hAppend]
  · simp [nil, HAppend.hAppend]
    nth_rw 2 [← Matrix.empty_vecAppend Γ.nth]
    grind

@[simp]
lemma FormulaContext.snoc_append {n : ℕ} (φᵢ : Fin (n + 1) → Formula κ xs) :
    (Γ ++ { length := n, nth := Matrix.vecInit φᵢ}).snoc (Matrix.vecLast φᵢ) =
    Γ ++ { length := n + 1, nth := φᵢ } := by
  ext
  · simp [HAppend.hAppend, FormulaContext.snoc]; omega
  · simp [HAppend.hAppend, FormulaContext.snoc]
    rw [← Matrix.vecLast_Append (n := Γ.length) (m := n) Γ.nth φᵢ,
      ← Matrix.vecAppend_init, Matrix.snoc_last_init]

variable (S) (κ) in
/-- A sequent is a pair of formulas (the premise and the conclusion) on a same context. -/
structure Sequent where
  ctx : S.Context
  premise : Formula κ ctx
  concl : Formula κ ctx

variable (S) (κ) in
/-- A `Theory` is a set of sequents, which are to be taken as the axioms of the theory. -/
abbrev Theory := Set (S.Sequent κ)
