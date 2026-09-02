import Isotope.LambdaIter.Named.ToLocallyNameless
import Isotope.LambdaIter.Typing
import Isotope.LambdaIter.Semantics.Categorical

/-! # Exact typed named-to-locally-nameless translation -/

universe v₁ v₂ u₁ u₂ v r

namespace Isotope.LambdaSSA.Translation.Frontend.NamedToLocallyNameless

open Isotope.LambdaIter

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

abbrev Scope := LambdaIter.Named.ToLocallyNameless.Scope

def Aligned (Γ : Ctx ν τ) (ρ : Scope ν n)
    (β : LambdaIter.LocallyNameless.BoundCtx τ n) (Δ : Ctx ν τ) : Prop :=
  ∀ {x A}, Δ.lookup x = some A →
    match ρ.resolve x with
    | .inl i => β.get i = A
    | .inr y => Γ.lookup y = some A

theorem Aligned.nil (Γ : Ctx ν τ) : Aligned Γ .nil .nil Γ := fun h => h

theorem Aligned.push (h : Aligned Γ ρ β Δ)
    (q : LambdaIter.Named.Binder ν) (A : τ) :
    Aligned Γ (.push q ρ) (.snoc β A) (.snoc Δ q A) := by
  intro x B hx
  cases q with
  | none =>
      simp only [Ctx.lookup] at hx
      rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_none]
      cases hr : ρ.resolve x <;> simpa [hr] using h hx
  | some y =>
      by_cases e : x = y
      · subst x
        have hAB : A = B := by simpa [Ctx.lookup] using hx
        simpa [LambdaIter.LocallyNameless.BoundCtx.get, hAB]
      · have hx' : Δ.lookup x = some B := by simpa [Ctx.lookup, e] using hx
        rw [LambdaIter.Named.ToLocallyNameless.Scope.resolve_push_ne _ e]
        cases hr : ρ.resolve x <;> simpa [hr] using h hx'

/-- Exact named typing translates to an exact locally nameless witness.  The
witness is proposition-truncated at the Prop-to-Type boundary. -/
theorem translateHasType {ρ : Scope ν n}
    {β : LambdaIter.LocallyNameless.BoundCtx τ n} {Γ Δ : Ctx ν τ}
    {t : LambdaIter.Named.Tm ν Φ} {A : τ} (hρ : Aligned Γ ρ β Δ)
    (h : LambdaIter.Named.HasType Φ Δ t A) :
    Nonempty (LambdaIter.LocallyNameless.HasType Φ Γ β
      (LambdaIter.Named.ToLocallyNameless.translate ρ t) A) := by
  induction h generalizing n ρ β Γ with
  | var hx =>
      unfold LambdaIter.Named.ToLocallyNameless.translate
      split <;> rename_i hr
      · have ht := hρ hx; rw [hr] at ht; exact ⟨ht ▸ .bv⟩
      · have ht := hρ hx; rw [hr] at ht; exact ⟨.fv ht⟩
  | op _ ih => exact (ih hρ).map LambdaIter.LocallyNameless.HasType.op
  | let₁ _ _ iha ihb =>
      obtain ⟨ha⟩ := iha hρ
      obtain ⟨hb⟩ := ihb (Aligned.push hρ _ _)
      exact ⟨.let₁ ha hb⟩
  | unit => exact ⟨.unit⟩
  | pair _ _ iha ihb =>
      obtain ⟨ha⟩ := iha hρ
      obtain ⟨hb⟩ := ihb hρ
      exact ⟨.pair ha hb⟩
  | let₂ _ _ iha ihb =>
      obtain ⟨ha⟩ := iha hρ
      obtain ⟨hb⟩ := ihb (Aligned.push (Aligned.push hρ _ _) _ _)
      exact ⟨.let₂ ha hb⟩
  | inl _ ih => exact (ih hρ).map LambdaIter.LocallyNameless.HasType.inl
  | inr _ ih => exact (ih hρ).map LambdaIter.LocallyNameless.HasType.inr
  | case _ _ _ ihe ihl ihr =>
      obtain ⟨he⟩ := ihe hρ
      obtain ⟨hl⟩ := ihl (Aligned.push hρ _ _)
      obtain ⟨hr⟩ := ihr (Aligned.push hρ _ _)
      exact ⟨.case he hl hr⟩
  | abort _ ih => exact (ih hρ).map LambdaIter.LocallyNameless.HasType.abort
  | iter _ _ iha ihb =>
      obtain ⟨ha⟩ := iha hρ
      obtain ⟨hb⟩ := ihb (Aligned.push hρ _ _)
      exact ⟨.iter ha hb⟩

theorem translateHasTypeClosed {Γ : Ctx ν τ} {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ Γ t A) :
    Nonempty (LambdaIter.LocallyNameless.HasType Φ Γ .nil
      (LambdaIter.Named.ToLocallyNameless.translateClosed t) A) :=
  translateHasType (Aligned.nil Γ) h

/-- A stable API for the witness hidden by `translateHasTypeClosed`. -/
noncomputable def chooseHasTypeClosed {Γ : Ctx ν τ}
    {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ Γ t A) :
    LambdaIter.LocallyNameless.HasType Φ Γ .nil
      (LambdaIter.Named.ToLocallyNameless.translateClosed t) A :=
  Classical.choice (translateHasTypeClosed h)

section Categorical

open CategoryTheory CategoryTheory.Limits

variable [Subtyping τ]

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  (M : LambdaIter.Subtyping.Semantics.Categorical.TypeModel τ V)
  [LambdaIter.Subtyping.Semantics.Categorical.InstructionModel J M Φ]

/-- Closed named exact terms are assigned the denotation of the chosen
locally-nameless typing witness. -/
noncomputable def denoteClosedChosen {Γ : Ctx ν τ}
    {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ Γ t A) :=
  LambdaIter.LocallyNameless.Categorical.denote J M (chooseHasTypeClosed h)

/-- Exact typing coherence makes the categorical denotation independent of
which witness of the proposition-truncated translation is selected. -/
theorem denoteClosedChosen_independent
    [LambdaIter.LocallyNameless.Categorical.TypingCoherent
      (ν := ν) (Φ := Φ) J M]
    {Γ : Ctx ν τ} {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ Γ t A)
    (k : LambdaIter.LocallyNameless.HasType Φ Γ .nil
      (LambdaIter.Named.ToLocallyNameless.translateClosed t) A) :
    LambdaIter.LocallyNameless.Categorical.denote J M k =
      denoteClosedChosen J M h :=
  LambdaIter.LocallyNameless.Categorical.TypingCoherent.denote_eq
    k (chooseHasTypeClosed h)

end Categorical

section Monadic

variable [Subtyping τ]
variable [Subtyping.Semantics.TypeModel.{u, v} τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Isotope.Elgot.Iterate m]
variable [Subtyping.Semantics.InstructionModel Φ τ ε m]

/-- Monadic denotation of a closed named term through the canonical chosen
exact locally-nameless typing witness. -/
noncomputable def denoteClosedChosenMonadic {Γ : Ctx ν τ}
    {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ Γ t A)
    (γ : Subtyping.Semantics.CtxDen Γ) : m (Subtyping.Semantics.TyDen A) :=
  LambdaIter.Semantics.denote (ε := ε) (m := m) (chooseHasTypeClosed h)
    γ PUnit.unit

/-- The monadic named-to-locally-nameless square for any selected witness;
exact typing coherence makes the result independent of that selection. -/
theorem denoteClosedChosenMonadic_independent
    [LambdaIter.Semantics.TypingCoherent (τ := τ) (ν := ν) (Φ := Φ)
      (ε := ε) (m := m)]
    {Γ : Ctx ν τ} {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ Γ t A)
    (k : LambdaIter.LocallyNameless.HasType Φ Γ .nil
      (LambdaIter.Named.ToLocallyNameless.translateClosed t) A)
    (γ : Subtyping.Semantics.CtxDen Γ) :
    LambdaIter.Semantics.denote (ε := ε) (m := m) k γ PUnit.unit =
      denoteClosedChosenMonadic (ε := ε) (m := m) h γ := by
  have hk := LambdaIter.Semantics.TypingCoherent.denote_eq
    (τ := τ) (ε := ε) (m := m) k (chooseHasTypeClosed h)
  exact congrFun (congrFun hk γ) PUnit.unit

end Monadic

end Isotope.LambdaSSA.Translation.Frontend.NamedToLocallyNameless
