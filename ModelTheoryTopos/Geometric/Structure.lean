import Mathlib.Tactic.DepRewrite
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Subobject.Limits
import ModelTheoryTopos.Geometric.Syntax.Formula
import ModelTheoryTopos.Geometric.Syntax.Derivation
import ModelTheoryTopos.Geometric.RegularCategory
import ModelTheoryTopos.ForMathlib.Subobject
import ModelTheoryTopos.ForMathlib.Miscellaneous

/-!
# The interpretation of the syntax into the semantics

In this file we show how to interpret the syntax of geometric logic into geometric category.
Our main result is `Soundness`, which shows that this interpretation is sound.

We introduce the following notation to interpret different syntax:
- `⟦ M | A⟧ˢ`  => Interpretation of sorts.
- `⟦ M | A⟧ᵈ`  => Interpretation of derived sorts.
- `⟦ M | xs⟧ᶜ` => Interpretation of (term) contexts.
- `⟦ M | σ⟧ʰ`  => Interpretation of (term) context morphisms.
- `⟦ M | P⟧ᶠ`  => Interpretation of formulas.
- `⟦ M | Γ⟧ᶠᶜ` => Interpretation of formula contexts.
-/

open CategoryTheory Limits Signature Geometric
namespace Signature

universe u v

section
variable {S : Signature} {C : Type u} [Category.{v} C] [HasFiniteProducts C]

/--
Given a category `C` and a function `Sorts → C` for an arbitrary type `Sorts`, we can
make a function `DerivedSorts Sorts → C` by mapping each tuple to the product of its entries.
-/
@[simp, reducible]
noncomputable def DerivedSorts.interpret {Sorts : Type*} (f : Sorts → C) :
    DerivedSorts Sorts → C := fun
  | .inj x => f x
  | .prod fᵢ => ∏ᶜ (fun i ↦ DerivedSorts.interpret f (fᵢ i))

variable (S) (C) in
/--
A structure for a signature `S` in a category `C` consists of an assignment of each sort of `S` to
an object of `C`, as well as an assignment of each function symbol to a morphism, and finally an
assignment of each relation symbol to a subobject of the appropriate sort.
-/
structure Structure where
  sorts : S.Sorts → C
  Functions (f : S.Functions) : f.domain.interpret sorts ⟶ f.codomain.interpret sorts
  Relations (R : S.Relations) : Subobject <| R.domain.interpret sorts

noncomputable section

variable (M : Structure S C) {ys xs : S.Context} (σ : ys ⟶ xs)

notation3:arg "⟦" M "|" A "⟧ᵈ" => DerivedSorts.interpret (Structure.sorts M) A

/-- The interpretation of a context is the product of the interpretation of each sort in it. -/
@[reducible]
def Context.interpret (xs : S.Context) : C :=
  ∏ᶜ (fun i ↦ ⟦M | xs.nth i⟧ᵈ)

notation3:arg "⟦" M "|" xs "⟧ᶜ" => Context.interpret M xs
notation3:arg "⟦" M "|" A "⟧ˢ" => Structure.sorts (self := M) A

/-- The interpretation of a term, by cases. -/
@[reducible]
def Term.interpret {A : S} :
    ⊢ᵗ[xs] A → (⟦M | xs⟧ᶜ ⟶ (⟦M | A⟧ᵈ))
  | .var v => Pi.π (fun i ↦ ⟦M | xs.nth i⟧ᵈ) v
  | .func f t => t.interpret ≫ M.Functions f
  | pair tᵢ => Pi.lift fun i ↦ (tᵢ i).interpret
  | proj (Aᵢ := Aᵢ) t i => t.interpret ≫ Pi.π (fun i ↦ ⟦M | Aᵢ i⟧ᵈ) i

notation3:arg "⟦" M "|" t "⟧ᵗ" =>
  Term.interpret M t

@[simp]
lemma Term.eqToHom_sort {A B : S} (p : A = B) (t : ⊢ᵗ[xs] A) :
    ⟦M| p ▸ t⟧ᵗ = ⟦M | t⟧ᵗ ≫ eqToHom (p ▸ rfl : ⟦M|A⟧ᵈ=⟦M|B⟧ᵈ) := by
  induction p; simp

lemma Term.interpret_var {A : S} : ⟦M|ys.var A⟧ᵗ = Pi.π _ 0 := rfl

@[simp]
lemma Term.interpret_pair_proj {xs n} {Aᵢ : (i : Fin n) → S}
    (tᵢ : (i : Fin n) → ⊢ᵗ[xs] (Aᵢ i)) {i : Fin n} :
    ⟦M|(Term.pair tᵢ).proj i⟧ᵗ = ⟦M|tᵢ i⟧ᵗ := by simp

@[simp]
lemma Term.interpret_proj {xs n} {Aᵢ : (i : Fin n) → S} (t : ⊢ᵗ[xs] .prod Aᵢ) :
    ⟦M|Term.pair (fun i ↦ t.proj i)⟧ᵗ = ⟦M|t⟧ᵗ := by
  apply Pi.hom_ext; simp

lemma Term.interpret_nthTerm {i : Fin xs.length} :
    ⟦M|xs.nthTerm i⟧ᵗ = Pi.π _ i := by
  simp [Context.nthTerm]

/-- The interpretation of a context morphism. -/
@[reducible]
def Context.Hom.interpret : ⟦M | ys⟧ᶜ ⟶ ⟦M | xs⟧ᶜ := Pi.lift (fun i ↦ ⟦M | σ i⟧ᵗ)

notation3:arg "⟦" M "|" σ "⟧ʰ" => Context.Hom.interpret M σ

@[simp]
lemma Context.Hom.interpret_id : ⟦M | 𝟙 xs⟧ʰ = 𝟙 ⟦M | xs⟧ᶜ := by
  refine Pi.hom_ext _ _ (fun i ↦ ?_)
  simp [CategoryStruct.id, Context.nthTerm, Term.interpret]

lemma Term.interpret_π : ⟦M|xs.π A i⟧ᵗ = Pi.π _ i.succ := by
  simp [Context.π, interpret]

@[simp]
lemma Context.Hom.interpret_subst {A : S} (t : ⊢ᵗ[xs] A) :
    ⟦M | t.subst σ⟧ᵗ = ⟦M | σ⟧ʰ ≫ ⟦M | t⟧ᵗ := by
  induction t with
  | var v => aesop
  | func f s ih =>
      simp only [Term.interpret, Context.Hom.interpret]
      rw [← Category.assoc]; congr
  | pair tᵢ =>
      simp only [Term.interpret, Context.Hom.interpret]
      ext; simp_all
  | proj t i =>
      simp only [Term.interpret, Context.Hom.interpret]
      rw [← Category.assoc]; congr

/--
The interpretation of an extended context is isomorphic to the interpretation of the context times
the interpretation of the new sort.
-/
def Context.interpretConsIso (xs : S.Context) (A : S) :
  ⟦M | A ∶ xs⟧ᶜ ≅ ⟦M | A⟧ᵈ ⨯ ⟦M | xs⟧ᶜ where
  hom := prod.lift (Pi.π _ 0) (Pi.lift (fun i ↦ Pi.π _ i.succ))
  inv := Pi.lift (Fin.cases prod.fst (fun i ↦ prod.snd ≫ Pi.π _ i))
  hom_inv_id := by apply Pi.hom_ext; intro i; cases i using Fin.cases <;> simp

lemma Context.interpretConsIso_naturality {ys xs : S.Context} (σ : ys ⟶ xs) {A : S} :
    prod.map (𝟙 _) ⟦M|σ⟧ʰ ≫ (interpretConsIso M xs A).inv =
      (interpretConsIso M ys A).inv ≫ ⟦M|(consFunctor A).map σ⟧ʰ := by
  apply Pi.hom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [interpretConsIso, consFunctor, Hom.cons, Term.interpret_var]
  | succ i =>
    simp [interpretConsIso, consFunctor, Hom.cons, CategoryStruct.comp]
    rw [← Category.assoc]
    congr
    apply (cancel_epi (interpretConsIso M ys A).hom).mp
    simp [interpretConsIso]
    apply Pi.hom_ext
    simp [Context.π, Term.interpret]

@[simp]
lemma Context.interpretConsIsoCompπ {A : S} :
    (Context.interpretConsIso M xs A).inv ≫ ⟦M|xs.π A⟧ʰ = prod.snd := by
  apply Pi.hom_ext
  intro i
  simp [Context.interpretConsIso]
  simp [Term.interpret_π]

lemma Context.Hom.consIdCompπ {A : S} (t : ⊢ᵗ[xs] A) : ⟦M|t⟧ᵗ = ⟦M|consId t⟧ʰ ≫ (Pi.π _ 0) := by
  simp [consId, cons]

lemma Context.Hom.consId_equalizer {A : S} {t1 t2 : ⊢ᵗ[xs] A}
    [HasEqualizer ⟦M|consId t1⟧ʰ ⟦M|consId t2⟧ʰ] [HasEqualizer ⟦M|t1⟧ᵗ ⟦M|t2⟧ᵗ] :
    equalizerSubobject ⟦M|Context.Hom.consId t1⟧ʰ ⟦M|Context.Hom.consId t2⟧ʰ =
      equalizerSubobject ⟦M|t1⟧ᵗ ⟦M|t2⟧ᵗ := by
  refine Subobject.skeletal _ ⟨iso_of_both_ways (Subobject.homOfFactors ?_) (Subobject.homOfFactors ?_)⟩
  · apply equalizerSubobject_factors
    rw [Context.Hom.consIdCompπ, Context.Hom.consIdCompπ, equalizerSubobject_arrow_comp_assoc]
  · apply equalizerSubobject_factors
    apply Pi.hom_ext
    intro i
    simp
    cases i using Fin.cases with
    | zero => simp [consId, cons]; exact equalizerSubobject_arrow_comp ⟦M|t1⟧ᵗ ⟦M|t2⟧ᵗ
    | succ i => simp [consId, cons]

@[simp]
lemma Term.interpret_subst
    {ys xs : Context S} (σ: ys ⟶ xs) {A : S} (t : ⊢ᵗ[xs] A) :
    ⟦M | t.subst σ⟧ᵗ = ⟦M|σ⟧ʰ ≫ ⟦M | t⟧ᵗ := by
  induction t with
  | var _ => simp
  | func f _ _ => simp [interpret]
  | pair tᵢ h =>
      simp only [DerivedSorts.interpret, interpret, Context.Hom.interpret_subst]
      rw [← funext h]; ext; simp
  | proj t i h => simp [interpret]

@[simp]
lemma Context.Hom.interpret_comp (σ : xs ⟶ ys) (σ' : ys ⟶ zs) :
  ⟦M | σ ≫ σ'⟧ʰ = ⟦M | σ⟧ʰ ≫ ⟦M | σ'⟧ʰ := by
  apply Pi.hom_ext
  intro i
  simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Category.assoc]
  rw [← Term.interpret_subst]
  rfl

lemma Context.consFunctor_IsPullback {ys xs : S.Context} (σ : ys ⟶ xs) {A : S} :
    IsPullback ⟦M|ys.π A⟧ʰ ⟦M|(Context.consFunctor A).map σ⟧ʰ ⟦M|σ⟧ʰ ⟦M|xs.π A⟧ʰ := by
    fapply IsPullback.of_iso <| IsPullback.of_prod_fst_with_id ⟦M|σ⟧ʰ ⟦M|A⟧ᵈ <;> try simp -- ASK: why simp not triggering?
    · exact prod.braiding _ _ ≪≫ (Context.interpretConsIso M ys A).symm
    · exact Iso.refl _
    · exact prod.braiding _ _ ≪≫ (Context.interpretConsIso M xs A).symm
    · exact Iso.refl _
    · apply Pi.hom_ext
      intro i
      simp [Term.interpret_π, interpretConsIso]
    · simp only [Iso.trans_hom, prod.braiding_hom, Iso.symm_hom, Category.assoc]
      rw [← Context.interpretConsIso_naturality, ← Category.assoc]
      simp
    · simp
    · simp
      rw [Context.interpretConsIsoCompπ] -- Why is this not simped above?
      simp

end

variable {S : Signature} {C : Type u} [Category.{v} C]
variable [κ : SmallUniverse S] [G : Geometric κ C] (M : Structure S C)

/-- The interpretation of a formula, by cases. -/
@[reducible, simp]
noncomputable def Formula.interpret {xs : Context S} : xs ⊢ᶠ𝐏 →
    (Subobject ⟦M | xs⟧ᶜ)
  | .rel R t => (Subobject.pullback ⟦M | t⟧ᵗ).obj <| M.Relations R
  | .true => ⊤
  | .false => ⊥
  | .conj φ ψ => φ.interpret ⨯ ψ.interpret
  | .eq t1 t2 => equalizerSubobject ⟦M | t1⟧ᵗ ⟦M | t2⟧ᵗ
  | .exists (A := A) φ => (Subobject.exists ((xs.π A).interpret M)).obj φ.interpret
  | .infdisj φᵢ => ∐ (fun i ↦ Formula.interpret (φᵢ i))

notation3:arg "⟦" M "|" φ "⟧ᶠ" =>
  Formula.interpret M φ

@[simp]
lemma Formula.interpret_subst
    {ys xs : Context S} (σ : ys ⟶ xs) (φ : xs ⊢ᶠ𝐏) :
    ⟦M | φ.subst σ⟧ᶠ = (Subobject.pullback ⟦M|σ⟧ʰ).obj ⟦M | φ⟧ᶠ := by
  induction φ generalizing ys with
  | rel R t => simp [Subobject.pullback_comp]
  | true => simp [Subobject.pullback_top]
  | false => simp [bot_isStableUnderBaseChange (κ := κ)]
  | conj P Q hp hq => simp [interpret, hp, hq, Subobject.prod_eq_inf, Subobject.inf_pullback]
  | infdisj fP h =>
      simp only [interpret]
      rw [← G.isJoin_isStableUnderBaseChange]
      have := funext (fun i ↦ h i σ)
      congr
  | eq t1 t2 =>
      simp only [interpret]
      rw [Limits.pullback_equalizer]
      congr <;> simp
  | @«exists» A xs φ hp =>
      simp only [interpret]
      rw [hp ((Context.consFunctor A).map σ)]
      apply Regular.frobenius_reciprocity (h := Context.consFunctor_IsPullback _ _)

/--
A model interprets a sequent if the interpretation of the premise is less than the interpretation of
the conclusion in the poset of subobjects.
-/
def Sequent.interpret (U : S.Sequent) : Prop :=
  ⟦M | U.premise⟧ᶠ ≤ ⟦M | U.concl⟧ᶠ

/-- A model interprets a theory if it interprets all of its sequents. -/
def Theory.interpret (T : S.Theory) : Prop := ∀ Seq ∈ T.axioms, Seq.interpret M

/--
The interpretation of a formula context, which is the product of the interpretation of all its
formulas.
-/
@[reducible]
noncomputable def FormulaContext.interpret
    {xs : Context S} (Γ : FormulaContext xs) : Subobject ⟦M|xs⟧ᶜ :=
  ∏ᶜ (fun i ↦ ⟦M | Γ.nth i⟧ᶠ)

notation3:arg "⟦" M "|" Γ "⟧ᶠᶜ" => FormulaContext.interpret (M := M) Γ

@[simp]
lemma FormulaContext.interpret_append
    {xs : Context S} (Γ Δ : FormulaContext xs) :
    ⟦M|Γ ++ Δ⟧ᶠᶜ = (⟦M|Γ⟧ᶠᶜ ⨯ ⟦M|Δ⟧ᶠᶜ) := by
  apply Subobject.skeletal_subobject
  simp [interpret]
  constructor
  apply iso_of_both_ways
    ( prod.lift
      ( Pi.lift <| fun i ↦
        append_nth_l Γ _ _ ▸ Pi.π (fun i ↦ ⟦M|(Γ ++ Δ).nth i⟧ᶠ) ⟨i, by simp; omega⟩)
      ( Pi.lift <| fun i ↦
        append_nth_r Γ _ _ ▸ Pi.π (fun i ↦ ⟦M|(Γ ++ Δ).nth i⟧ᶠ) ⟨Γ.length + i, by simp⟩))
  apply Pi.lift
  intro ⟨i, i_leq⟩
  by_cases h : i < Γ.length
  · refine prod.fst ≫ Pi.π _ ⟨i, h⟩ ≫ eqToHom ?_
    rw [FormulaContext.append_nth_l'']
  · let k : ℕ := i - Γ.length
    have p : i = Γ.length + k := by aesop
    have k_leq : k < Δ.length := by
      simp [append_length] at i_leq
      omega
    refine prod.snd ≫ Pi.π _ ⟨k, k_leq⟩ ≫ eqToHom ?_
    have : Δ.nth ⟨k, k_leq⟩ = (Γ ++ Δ).nth ⟨Γ.length + k, p ▸ i_leq⟩ := by
      rw [FormulaContext.append_nth_r'']
    rw [this]
    congr
    exact p.symm

@[simp]
lemma FormulaContext.interpret_cons
    {xs : Context S} (Γ : FormulaContext xs) (φ : xs ⊢ᶠ𝐏) :
    ⟦M|Γ.cons φ⟧ᶠᶜ = (⟦M|Γ⟧ᶠᶜ ⨯ ⟦M|φ⟧ᶠ) := by
  apply Subobject.skeletal_subobject
  simp [interpret]
  constructor
  apply iso_of_both_ways
  · apply prod.lift
    · exact Pi.lift <| fun i ↦ Pi.π (fun i ↦ ⟦M|(Γ.cons φ).nth i⟧ᶠ) i.succ
    · let proj := Pi.π (fun i ↦ ⟦M|(Γ.cons φ).nth i⟧ᶠ)
      simp [cons] at proj
      exact proj 0
  · apply Pi.lift
    intro b
    cases b using Fin.cases
    · simpa using prod.snd
    · simp only [Matrix.cons_val_succ]
      refine prod.fst (X := ∏ᶜ fun i ↦ ⟦M|Γ.nth i⟧ᶠ) (Y := ⟦M|φ⟧ᶠ) ≫ ?_
      apply Pi.π

lemma FormulaContext.interpret_cons_pullback
    {xs : Context S} (Γ : FormulaContext xs) (P : xs ⊢ᶠ𝐏) :
    ⟦M|Γ.cons P⟧ᶠᶜ = (Subobject.map (⟦M|Γ⟧ᶠᶜ).arrow).obj
      (((Subobject.pullback (⟦M|Γ⟧ᶠᶜ).arrow).obj ⟦M|P⟧ᶠ)) := by
  rw [FormulaContext.interpret_cons, ← Subobject.inf_eq_map_pullback'', Subobject.prod_eq_inf]

lemma FormulaContext.interpret_subst
    {xs ys : Context S} (Γ : FormulaContext xs) (σ : ys ⟶ xs) :
    ⟦M|Γ.subst σ⟧ᶠᶜ = (Subobject.pullback ⟦M|σ⟧ʰ).obj ⟦M|Γ⟧ᶠᶜ := by
  simp [FormulaContext.interpret, FormulaContext.subst_nth, Subobject.prod_pullback]
  rfl

lemma FormulaContext.interpret_cons_join
    {xs : Context S} (Γ : FormulaContext xs) {I : Set κ} (Pᵢ : I → xs ⊢ᶠ𝐏) :
    ⟦M|Γ.cons (⋁' Pᵢ)⟧ᶠᶜ = ∐ fun i ↦ ⟦M|Γ.cons (Pᵢ i)⟧ᶠᶜ := by
  rw [FormulaContext.interpret_cons]
  rw [Formula.interpret]
  rw [Geometric.inf_join_eq_join_inf]
  congr
  funext; simp

/--
If there is a derivation of a formula `φ` in context `Γ`, then it is the case that
`⟦M | Γ⟧ᶠᶜ ≤ ⟦M | φ⟧ᶠ` whenever the model `M` satisfies all the axioms in theory.
-/
theorem Soundness {T : S.Theory} {xs : Context S} {Γ : FormulaContext xs} {φ : xs ⊢ᶠ𝐏} :
  Derivation (T := T) Γ φ → Theory.interpret M T →
    (⟦M | Γ⟧ᶠᶜ ≤ ⟦M | φ⟧ᶠ) := by
  intro D int
  induction D with
  | «axiom» φinT D hp =>
      apply le_trans hp; simp only [Formula.interpret_subst];
      apply Functor.monotone; exact int _ φinT
  | @var xs Γ i => exact (Pi.π (fun i ↦ ⟦M|Γ.nth i⟧ᶠ) i).le
  | true_intro => simp
  | false_elim D h => rw [bot_unique h]; simp
  | conj_intro D D' h h' => exact (prod.lift h.hom h'.hom).le
  | conj_elim_l D h => exact (h.hom ≫ prod.fst).le
  | conj_elim_r D h => exact (h.hom ≫ prod.snd).le
  | disj_intro Pᵢ i D h => exact (h.hom ≫ Sigma.ι (fun i ↦ ⟦M|Pᵢ i⟧ᶠ) i).le
  | @disj_elim xs Γ Q I Pᵢ D Dᵢ h h' =>
      apply leOfHom
      refine ?_ ≫ eqToHom (Γ.interpret_cons_join M Pᵢ) ≫ Sigma.desc (fun b ↦ (h' b).hom)
      simp only [FormulaContext.interpret_cons]
      exact prod.lift (𝟙 _) h.hom
  | eq_intro => simp [FormulaContext.interpret]
  | @eq_elim xs A t1 t2 Γ Γ' φ D_eq D' h h' =>
      simp at *
      refine Subobject.le_of_comm ?_ ?_
      · apply (Subobject.isPullback _ _).lift
          ((Subobject.ofLE _ _ h') ≫ (Subobject.pullbackπ _ _)) (⟦M|Γ'⟧ᶠᶜ ⨯ ⟦M|Γ⟧ᶠᶜ).arrow
        rw [Category.assoc, (Subobject.isPullback _ _).w, Subobject.ofLE_arrow_assoc]
        rw [← Context.Hom.consId_equalizer] at h
        have :
          (⟦M|Γ'⟧ᶠᶜ ⨯ ⟦M|Γ⟧ᶠᶜ).arrow =
          Subobject.ofLE _ _ (leOfHom (prod.snd (X := ⟦M|Γ'⟧ᶠᶜ) (Y := ⟦M|Γ⟧ᶠᶜ))) ≫
            Subobject.ofLE _ _ h ≫
            (equalizerSubobject ⟦M|Context.Hom.consId t1⟧ʰ ⟦M|Context.Hom.consId t2⟧ʰ).arrow := by
          simp
        rw [this, Category.assoc, Category.assoc, Limits.equalizerSubobject_arrow_comp]
        simp
      · simp
  | @eq_proj_pair xs n A tᵢ i Γ => simp
  | @eq_pair_proj xs n Aᵢ t Γ =>
      have : IsIso (equalizer.ι ⟦M|Term.pair fun i ↦ t.proj i⟧ᵗ ⟦M|t⟧ᵗ) :=
        equalizer.ι_of_eq <| Term.interpret_proj M t
      simp [CategoryTheory.Subobject.mk_eq_top_of_isIso]
  | @exists_intro xs A Γ φ t D h =>
      rw [Formula.interpret_subst] at h
      refine le_trans h ?_
      apply Subobject.le_of_comm ((Subobject.pullbackπ _ _) ≫ (Subobject.imageFactorisation _ _).F.e)
      have :
        ((Subobject.exists ⟦M|xs.π A⟧ʰ).obj ⟦M|φ⟧ᶠ).arrow =
          (Subobject.imageFactorisation ⟦M|xs.π A⟧ʰ ⟦M|φ⟧ᶠ).F.m := rfl
      rw [Category.assoc, this, (Subobject.imageFactorisation ⟦M|xs.π A⟧ʰ ⟦M|φ⟧ᶠ).F.fac]
      rw [(Subobject.isPullback _ _).w_assoc, ← Context.Hom.interpret_comp]
      simp
  | @exists_elim xs A Γ φ D_exists ψ D ih_exists ih_D =>
      apply le_trans (leOfHom <| prod.lift (homOfLE ih_exists) (𝟙 _))
      rw [Subobject.prod_eq_inf, ← Regular.exists_inf_pullback_eq_exists_inf,
        ← Subobject.prod_eq_inf]
      apply leOfHom
      apply (Adjunction.homEquiv (Subobject.existsPullbackAdj ⟦M|xs.π A⟧ʰ)
        (⟦M|φ⟧ᶠ ⨯ (Subobject.pullback ⟦M|xs.π A⟧ʰ).obj ⟦M|Γ⟧ᶠᶜ) ⟦M|ψ⟧ᶠ).invFun
      rw [Formula.interpret_subst] at ih_D
      refine eqToHom ?_≫ homOfLE ih_D
      rw [FormulaContext.interpret_cons, FormulaContext.interpret_subst]
      rw [Subobject.prod_eq_inf, Subobject.prod_eq_inf, inf_comm]

end
end Signature
