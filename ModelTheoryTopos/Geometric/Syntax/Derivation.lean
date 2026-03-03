import ModelTheoryTopos.Geometric.Syntax.Formula

/-!
# Derivations

In this file we define derivations, given in a natural deduction style. We show that derivation are
stable under substitution.
-/

open CategoryTheory Limits

namespace Signature

variable {S : Signature} {κ : Cardinal.{w}} [κ_isRegular : Fact κ.IsRegular] {T : S.Theory κ}

variable (κ T) in
/-- A natural deduction style definition of derivation. -/
inductive Derivation : {xs : S.Context} → FormulaContext κ xs → Formula κ xs → Type _ where
  | axiom {xs} {Γ : FormulaContext κ xs} {φ : S.Sequent κ} {σ : xs ⟶ φ.ctx}
      (φinT : φ ∈ T) (D : Derivation Γ (φ.premise.subst σ)) : Derivation Γ (φ.concl.subst σ)
  | var {xs} (Γ : S.FormulaContext κ xs) (i : Fin Γ.length) : Derivation Γ (Γ.nth i)
  | true_intro {xs} {Γ : FormulaContext κ xs} : Derivation Γ ⊤'
  | false_elim {xs} {Γ : FormulaContext κ xs} {φ : Formula κ xs} (D_false : Derivation Γ ⊥') :
      Derivation Γ φ
  | conj_intro {Γ φ ψ} (D_left : Derivation Γ φ) (D_right : Derivation Γ ψ) : Derivation Γ (φ ∧' ψ)
  | conj_elim_l {Γ φ ψ} (D_conj : Derivation Γ (φ ∧' ψ)) : Derivation Γ φ
  | conj_elim_r {Γ φ ψ} (D_conj : Derivation Γ (φ ∧' ψ)) : Derivation Γ ψ
  | disj_intro {xs Γ} {I : Type w} [Fact <| HasCardinalLT I κ] (φᵢ : I → S.Formula κ xs) (i : I) (D : Derivation Γ (φᵢ i)) :
      Derivation Γ (⋁' φᵢ)
  | disj_elim {xs Γ ψ} {I : Type w} [Fact <| HasCardinalLT I κ] {φᵢ : I → S.Formula κ xs} (D_disj : Derivation Γ (⋁' φᵢ))
    (Dᵢ : (i : I) → Derivation (Γ.cons (φᵢ i)) ψ) : Derivation Γ ψ
  | eq_intro {Γ t} : Derivation Γ (.eq t t)
  | eq_elim {xs A t1 t2} {Γ Γ' : S.FormulaContext κ xs} (φ : S.Formula κ (A ∶ xs))
    (D_eq : Derivation Γ (t1 =' t2)) (D : Derivation (Γ' ++ Γ) (φ.subst (Context.Hom.consId t1))) :
    Derivation (Γ' ++ Γ) (φ.subst (Context.Hom.consId t2))
  | eq_proj_pair {xs n} {Aᵢ : (i : Fin n) → S} (tᵢ : (i : Fin n) → ⊢ᵗ[xs] (Aᵢ i)) {i : Fin n} {Γ} :
      Derivation Γ ((Term.pair tᵢ).proj i =' tᵢ i)
  | eq_pair_proj {xs n} {Aᵢ : Fin n → DerivedSorts S.Sorts} (t : ⊢ᵗ[xs] .prod Aᵢ) {Γ} :
      Derivation Γ (Term.pair (fun i ↦ t.proj i) =' t)
  | exists_intro {xs A} {Γ : S.FormulaContext κ xs} (φ : S.Formula κ (A ∶ xs)) (t : S.Term xs A)
      (D : Derivation Γ (φ.subst (Context.Hom.consId t))) : Derivation Γ (∃' φ)
  | exists_elim {xs A} {Γ : S.FormulaContext κ xs} {φ : S.Formula κ (A ∶ xs)}
      (D_exists : Derivation Γ (∃' φ)) {ψ}
      (D : Derivation ((Γ.subst (xs.π A)).cons φ) (ψ.subst (xs.π A))) :
      Derivation Γ ψ


scoped syntax:25 term " ⊢ᵈ[ " term:51 " ] " term:50 : term
scoped syntax:25 term " ⊢ᵈ" term:50 : term

-- Hack to hardcode `κ` and `T`
scoped macro_rules
  | `($Γ ⊢ᵈ[ $xs ] $φ) =>  `(Derivation $(Lean.mkIdent `κ) $(Lean.mkIdent `T) (xs := $xs) $Γ $φ)
  | `($Γ ⊢ᵈ $φ) =>  `(Derivation $(Lean.mkIdent `κ) $(Lean.mkIdent `T) $Γ $φ)

variable {xs : S.Context} {Δ Γ : FormulaContext κ xs} {φ : Formula κ xs}

variable (T Δ Γ) in
/--
A morphism between Formula κ contexts `Δ ⟶ Γ` consists of a derivation of each Formula κ in `Γ`, from
the formulas in Δ
-/
def FormulaContext.Hom : Type _ :=
  (i : Fin Γ.length) → Δ ⊢ᵈ Γ.nth i

-- Sadly useless for notation as it depends on `T`, which usually can't be infered by the motive.
instance : Quiver (FormulaContext κ xs) where
  Hom := FormulaContext.Hom T

/-- The identity Formula κ context morphism. -/
def FormulaContext.Hom.Id (Γ : FormulaContext κ xs) : FormulaContext.Hom T Γ Γ := .var Γ

/-- The extension of a Formula κ context morphism by a new derivation. -/
def FormulaContext.Hom.cons (ξ : FormulaContext.Hom T Δ Γ) (D : Δ ⊢ᵈ φ) :
    FormulaContext.Hom T Δ (Γ.cons φ) :=
  Fin.cases D ξ

variable (Δ φ) in
/-- The projection Formula κ context morphism. -/
def FormulaContext.Hom.π : FormulaContext.Hom T (Δ.cons φ) Δ :=
  fun i ↦ .var (Δ.cons φ) i.succ

/-- Derivations can be substituded by context morphisms. -/
def Derivation.substContextHom {xs} {Γ : FormulaContext κ xs} {φ : Formula κ xs}
    (D : Γ ⊢ᵈ φ) : (ys : S.Context) → (ρ : ys ⟶ xs) → (Γ.subst ρ ⊢ᵈ φ.subst ρ) :=
  match D with
  | @«axiom» _ _ _ _ xs Γ ψ σ' φinT D => fun ys σ ↦ by
      let D' := substContextHom D _ σ
      rw [← Formula.subst_comp] at D' ⊢
      exact Derivation.axiom (T := T) φinT D'
  | var Γ i => fun ys σ ↦ Derivation.var (Γ.subst σ) i
  | true_intro => fun ys σ ↦ true_intro
  | false_elim D_false => fun ys σ ↦ false_elim (substContextHom D_false _ σ)
  | conj_intro D_left D_right => fun ys σ ↦
      conj_intro (substContextHom D_left _ σ) (substContextHom D_right _ σ)
  | conj_elim_l D_conj => fun ys σ ↦ conj_elim_l (substContextHom D_conj _ σ)
  | conj_elim_r D_conj => fun ys σ ↦ conj_elim_r (substContextHom D_conj _ σ)
  | disj_intro φᵢ i D => fun ys σ ↦ disj_intro _ i (substContextHom D _ σ)
  | disj_elim D_disj Dᵢ => fun ys σ ↦
      disj_elim
        (substContextHom D_disj _ σ)
        (fun i ↦ FormulaContext.subst_cons σ Γ _ ▸ substContextHom (Dᵢ i) _ σ)
  | eq_intro => fun ys σ ↦ eq_intro
  | @eq_elim _ _ _ _ xs A t1 t2 Γ Γ' φ D_eq D => fun ys σ ↦ by
      let D' := substContextHom D _ σ
      rw [FormulaContext.subst_append, ← Formula.subst_comp, Context.Hom.consId_naturality,
        Formula.subst_comp] at D' ⊢
      exact eq_elim _ (substContextHom D_eq _ σ) D'
  | eq_proj_pair tᵢ => fun ys σ ↦ eq_proj_pair _
  | eq_pair_proj t => fun ys σ ↦ eq_pair_proj _
  | exists_intro φ t D => fun ys σ ↦ by
      let D' := (substContextHom D _ σ)
      rw [← Formula.subst_comp, Context.Hom.consId_naturality, Formula.subst_comp] at D'
      exact exists_intro _ _ D'
  | exists_elim D_exists D => fun ys σ ↦ by
      apply Derivation.exists_elim (substContextHom D_exists _ σ)
      let D' := substContextHom D _ ((Context.consFunctor _).map σ)
      rw [FormulaContext.subst_cons, ← FormulaContext.subst_comp, ← Formula.subst_comp] at D'
      rw [← FormulaContext.subst_comp, ← Formula.subst_comp]
      exact D'

/--
Given a derivation of `φ` on context `Γ`, if `Γ ⊆' Δ` then we also have a derivation of `φ` in `Δ`.
-/
def Derivation.weakenFormulaContext {xs} {Γ : FormulaContext κ xs} {φ : Formula κ xs}
    (D : Γ ⊢ᵈ φ) : (Δ : FormulaContext κ xs) → (ξ : Γ ⊆' Δ) → Δ ⊢ᵈ φ :=
  match D with
  | @«axiom» _ _ _ _ xs Γ ψ σ φinT D => fun _ ξ ↦
      .axiom (T := T) φinT (.weakenFormulaContext D _ ξ)
  | @var _ _ _ _ xs Γ i => fun Δ ξ ↦
      let ⟨j, q⟩ := ξ (Γ.nth i) ⟨i, rfl⟩
      q ▸ .var Δ j
  | @true_intro _ _ _ _ xs Γ => fun _ _ ↦ .true_intro
  | @false_elim _ _ _ _ xs Γ φ D_false => fun _ ξ ↦ false_elim (.weakenFormulaContext D_false _ ξ)
  | @conj_intro _ _ _ _ xs Γ φ ψ D_left D_right => fun _ ξ ↦
      conj_intro (.weakenFormulaContext D_left _ ξ) (.weakenFormulaContext D_right _ ξ)
  | @conj_elim_l _ _ _ _  xs Γ φ ψ D_conj => fun _ ξ ↦ conj_elim_l (.weakenFormulaContext D_conj _ ξ)
  | @conj_elim_r _ _ _ _ xs Γ φ ψ D_conj => fun _ ξ ↦ conj_elim_r (.weakenFormulaContext D_conj _ ξ)
  | @disj_intro _ _ _ _ _ xs Γ I φᵢ i D => fun _ ξ ↦ disj_intro φᵢ i (.weakenFormulaContext D _ ξ)
  | @disj_elim _ _ _ _ _ xs Γ _ _ φᵢ D_disj Dᵢ  => fun Δ ξ ↦
      disj_elim (weakenFormulaContext D_disj _ ξ) fun i ↦
        (weakenFormulaContext (Dᵢ i) (Δ.cons (φᵢ i)) (FormulaContext.incl_cons_cons (φᵢ i) ξ))
  | @eq_intro _ _ _ _ xs A Γ t => fun _ _ ↦ eq_intro
  | @eq_elim _ _ _ _ xs A _ t2 Γ Γ' φ D_eq D  => fun Δ ξ ↦
    FormulaContext.nil_append (κ := κ) Δ ▸
      eq_elim φ (Γ' := .nil _) (.weakenFormulaContext D_eq _ (FormulaContext.append_incl_l ξ))
        (.weakenFormulaContext D _ (FormulaContext.nil_append (κ := κ) _ ▸ ξ))
  | @eq_proj_pair _ _ _ _ xs n Aᵢ tᵢ i Γ => fun _ _ ↦ eq_proj_pair tᵢ
  | @eq_pair_proj _ _ _ _ xs n Aᵢ t Γ => fun _ _ ↦ eq_pair_proj t
  | @exists_intro _ _ _ _ xs A Γ φ t D => fun _ ξ ↦ exists_intro φ t (.weakenFormulaContext D _ ξ)
  | @exists_elim _ _ _ _ xs _ Γ φ D_exists ψ D => fun _ ξ ↦
    exists_elim (.weakenFormulaContext D_exists _ ξ)
      (.weakenFormulaContext D _ (FormulaContext.incl_cons_cons φ (FormulaContext.incl_subst ξ _)))

/-- The functorial action of the `cons` operation on Formula κ context morphisms. -/
def Derivation.Hom.consMap {xs} {Δ Γ : FormulaContext κ xs} (φ : Formula κ xs)
    (ξ : FormulaContext.Hom T Δ Γ) :
    (Δ.cons φ).Hom (T := T) (Γ.cons φ) :=
  Fin.cases (.var _ 0) (fun i ↦ weakenFormulaContext (ξ i) _ (FormulaContext.incl_cons Δ φ))

/-- The functorial action of the `subst` operation on Formula κ context morphisms. -/
def Derivation.Hom.substMap {xs ys} {Δ Γ : FormulaContext κ xs} (σ : ys ⟶ xs)
    (ξ : FormulaContext.Hom T Δ Γ) :
    (Δ.subst σ).Hom (T := T) (Γ.subst σ) :=
  fun i ↦ substContextHom (ξ i) _ σ

/-- Derivations can be substituded by Formula κ context morphisms. -/
def Derivation.subst {xs} {Γ : FormulaContext κ xs} {φ : Formula κ xs}
    (D : Γ ⊢ᵈ φ) {Δ : FormulaContext κ xs} (ξ : FormulaContext.Hom T Δ Γ) : Δ ⊢ᵈ φ :=
  match D with
  | «axiom» φinT D => .axiom (T := T) φinT (subst D ξ)
  | var Γ i => ξ i
  | true_intro => true_intro
  | false_elim D_false => false_elim (subst D_false ξ)
  | conj_intro D_left D_right => conj_intro (subst D_left ξ) (subst D_right ξ)
  | conj_elim_l D_conj => conj_elim_l (subst D_conj ξ)
  | conj_elim_r D_conj => conj_elim_r (subst D_conj ξ)
  | disj_intro φᵢ i D => disj_intro _ _ (subst D ξ)
  | disj_elim D_disj Dᵢ =>
      disj_elim (subst D_disj ξ) fun i ↦ subst (Dᵢ i) (Derivation.Hom.consMap _ ξ)
  | eq_intro => eq_intro
  | @eq_elim _ _ _ _ _ A t1 t2 Γ' Γ φ D_eq D =>
      let Δ_t1_eq_t2 : Δ ⊢ᵈ t1 =' t2 :=
        subst D_eq (Δ := Δ) fun i ↦
          (FormulaContext.append_nth_r' (κ := κ) _ _ i _ ▸ ξ ⟨Γ.length + i, by simp⟩)
      let goal : FormulaContext.nil _ ++ Δ ⊢ᵈ φ.subst (Context.Hom.consId t2) :=
        eq_elim φ Δ_t1_eq_t2 <| (FormulaContext.nil_append Δ).symm ▸ subst D (ξ)
      FormulaContext.nil_append Δ ▸ goal
  | eq_proj_pair tᵢ => eq_proj_pair _
  | eq_pair_proj t => eq_pair_proj _
  | exists_intro φ t D => exists_intro φ t (subst D ξ)
  | exists_elim D_exists D =>
      Derivation.exists_elim (subst D_exists ξ)
      (subst D (Derivation.Hom.consMap _ (Derivation.Hom.substMap _ ξ)))

end Signature
