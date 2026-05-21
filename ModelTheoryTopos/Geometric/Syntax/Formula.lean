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

namespace Signature

open Cardinal CategoryTheory

variable {S : Signature}

class SmallUniverse (S : Signature) where
  type : Type*

attribute [coe] SmallUniverse.type

instance : CoeSort (SmallUniverse S) Type* where
  coe κ := κ.type

variable [κ : SmallUniverse S]

inductive Formula : S.Context → Type* where
  | rel {xs} (R : S.Relations) : Term xs (R.domain) → Formula xs
  | true {xs} : Formula xs
  | false {xs} : Formula xs
  | conj {xs} : Formula xs → Formula xs → Formula xs
  | infdisj {xs} {I : Set κ} : (I → Formula xs) → Formula xs
  | eq {xs A} : ⊢ᵗ[xs] A → ⊢ᵗ[xs] A → Formula xs
  | exists {A xs} : Formula (A ∶ xs) → Formula xs

scoped notation:max "⊤'" => Formula.true
scoped notation:max "⊥'" => Formula.false
scoped infixr:62 " ∧' " => Formula.conj
scoped prefix:100 "⋁'" => Formula.infdisj
scoped infixr:50 " =' " => Formula.eq
scoped prefix:110 "∃'" => Formula.exists
scoped prefix:110 "∀'" => Formula.forall
scoped infixr:55 "→'" => Formula.implies


scoped syntax:25 term:51 " ⊢ᶠ𝐏" : term
scoped macro_rules
  | `($xs ⊢ᶠ𝐏) => `(Formula $(Lean.mkIdent `κ) $xs) -- Hack to not reference κ

variable {κ : Cardinal.{w}} [κ_isRegular : Fact κ.IsRegular]

@[reducible]
def Formula.subst {ys xs : S.Context} (σ : ys ⟶ xs) (φ : xs ⊢ᶠ𝐏) : ys ⊢ᶠ𝐏 :=
  match φ with
  | rel R t => .rel R (t.subst σ)
  | ⊤' => ⊤'
  | ⊥' => ⊥'
  | φ ∧' ψ => (φ.subst σ) ∧' (ψ.subst σ)
  | ⋁' φᵢ => ⋁' (fun i ↦ (φᵢ i).subst σ)
  | t1 =' t2 => (t1.subst σ) =' (t2.subst σ)
  | ∃' φ => ∃' (φ.subst ((Context.consFunctor _).map σ))
  | ∀' φ => ∀' (φ.subst ((Context.consFunctor _).map σ))
  | φ →' ψ => (φ.subst σ) →' (ψ.subst σ)

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
  | «exists» φ h => simpa using h
  | «forall» φ h => simpa using h
  | implies _ _ h h' => simp [h, h']

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
  | @«forall» A zs φ h => simp; intro xs ys σ σ'; rw [← h]
  | implies _ _ h h' => simp [h, h']

@[ext]
structure FormulaContext (xs : S.Context) where
  length : ℕ
  nth : Fin length → Formula κ xs

def FormulaContext.nil (xs : S.Context) : FormulaContext xs where
  length := 0
  nth := ![]

variable {ys xs : S.Context} (Γ : FormulaContext κ xs)

@[simp]
lemma FormulaContext.length_0_isNil (φ : Fin 0 → Formula κ xs) :
    FormulaContext.mk 0 φ = FormulaContext.nil xs := by
  ext <;> simp [nil]; ext i; exact Fin.elim0 i

@[reducible]
def FormulaContext.cons (φ : Formula κ xs) : FormulaContext κ xs where
  length := Γ.length + 1
  nth := Matrix.vecCons φ Γ.nth

@[simp]
lemma FormulaContext.cons_nth0 (Γ : FormulaContext κ xs) (φ) : (Γ.cons φ).nth 0 = φ := by simp

@[simp]
lemma FormulaContext.lenght_cons (φ : Formula κ xs) : (Γ.cons φ).length = Γ.length + 1 := by
  simp

def FormulaContext.snoc (φ : Formula xs) : FormulaContext xs where
  length := Γ.length + 1
  nth := Matrix.vecSnoc φ Γ.nth

def FormulaContext.subst (Γ : FormulaContext xs) (σ : ys ⟶ xs) : FormulaContext ys where
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

def FormulaContext.mem (φ : Formula xs) (Γ : FormulaContext (κ := κ) xs) : Type _ :=
  {i // Γ.nth i = φ}

scoped infixr:62 " ∈' " => FormulaContext.mem

def FormulaContext.mem_cons {Γ : FormulaContext (κ := κ) xs} {ψ : Formula xs} (ψinΓ : ψ ∈' Γ) (φ) :
  ψ ∈' Γ.cons φ := ⟨ψinΓ.1.succ, ψinΓ.2⟩

def FormulaContext.incl (Δ Γ : FormulaContext (κ := κ) xs) :=
  ∀ ψ, ψ ∈' Δ → ψ ∈' Γ

scoped infixr:62 " ⊆' " => FormulaContext.incl

def FormulaContext.incl_cons (Γ : FormulaContext (κ := κ) xs) (ψ : Formula xs) :
  Γ ⊆' (Γ.cons ψ) := fun _ ⟨i, p⟩ ↦ ⟨i.succ, p⟩

def FormulaContext.incl_subst {Δ Γ : FormulaContext (κ := κ) xs} (ξ : Δ ⊆' Γ) (σ : ys ⟶ xs) :
    Δ.subst σ ⊆' Γ.subst σ := fun ψ ⟨i, p⟩ ↦
  let ⟨j, k⟩ := ξ (Δ.nth i) ⟨i, rfl⟩
  ⟨j, by rw [FormulaContext.subst_nth, k, ← FormulaContext.subst_nth, p]⟩

def FormulaContext.incl_cons_cons {Δ Γ : FormulaContext (κ := κ) xs} (φ) (ξ : Δ ⊆' Γ) :
    Δ.cons φ ⊆' Γ.cons φ := fun ψ ⟨i, p⟩ ↦
  Fin.cases (motive := fun j ↦ (Δ.cons φ).nth j = ψ → ψ ∈' Γ.cons φ)
    (fun p ↦ p ▸ ⟨0, rfl⟩)
    (fun i p ↦ p ▸ FormulaContext.mem_cons (ξ (Δ.nth i) ⟨i, rfl⟩) φ)
    i p

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

variable (S) in
structure Sequent : Type* where
  ctx : S.Context
  premise : Formula κ ctx
  concl : Formula κ ctx

variable (S) in
class Theory where
  axioms : Set S.Sequent

attribute [coe] Theory.axioms

instance : Coe (Theory (κ := κ)) (Set S.Sequent) where
  coe T := T.axioms

instance instMembershipTheory : Membership (S.Sequent) (S.Theory (κ := κ)) := {
  mem T φ := φ ∈ T.axioms
}
