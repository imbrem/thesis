import Isotope.LambdaIter.Semantics.Kleisli.Soundness
import Isotope.LambdaIter.Semantics.Kleisli.Surjective
import Isotope.LambdaIter.Subtyping.Semantics.Agreement.Full
import Isotope.LambdaIter.Semantics.Soundness

/-!
# The Kleisli categorical model of lambda-iter

This file closes the gap recorded in the honest boundaries of the initiality
development: `Categorical.TypingCoherent` and `Categorical.LawfulModel` had no
instance anywhere, so no categorical model of lambda-iter had been delivered.

Both are established here for the Kleisli category of a lawful Elgot monad `m`
on `Type v`, with the value category `Type v` and the free Freyd embedding.  No
categorical calculation is redone: the agreement theorem
`Subtyping.Semantics.categorical_denote_eq` transports the monadic facts of
`Kleisli/Coherence.lean` and `Kleisli/Soundness.lean` across, once
`envToCategorical` is known to be onto.
-/

namespace Isotope.LambdaIter.Semantics

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless
open Isotope.Elgot
open CategoryTheory CategoryTheory.Limits

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]

/-- The Kleisli Freyd embedding of the type monad of `m`. -/
abbrev kleisliJ (m : Type v → Type v) [Monad m] [LawfulMonad m] :
    Functor (Type v) (Kleisli (CategoryTheory.ofTypeMonad m)) :=
  CategoryTheory.Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)

/-- **Pointwise determination of the categorical denotation.**  Two exact
derivations whose direct denotations agree at every environment have equal
categorical denotations, because `envToCategorical` is onto. -/
theorem denoteOfType_ext {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t t' : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A)
    (k : HasType Φ Γ β t' A)
    (H : ∀ (γ : CtxDen Γ) (ρ : BoundDen β),
      exactDenote (ε := ε) (m := m) h γ ρ =
        exactDenote (ε := ε) (m := m) k γ ρ) :
    Categorical.denoteOfType (ε := ε) (m := m) h.toGeneric =
      Categorical.denoteOfType (ε := ε) (m := m) k.toGeneric := by
  apply CategoryTheory.Kleisli.hom_ext
  funext e
  obtain ⟨γ, ρ, rfl⟩ := envToCategorical_surjective (τ := τ) (ν := ν) e
  rw [categorical_denote_eq (ε := ε) (m := m) h.toGeneric γ ρ,
    categorical_denote_eq (ε := ε) (m := m) k.toGeneric γ ρ]
  exact H γ ρ

section Coherent

variable [InjectiveFormers τ]

/-- **Typing coherence at the Kleisli model.**  The first instance of
`Categorical.TypingCoherent` anywhere in the development. -/
noncomputable instance instTypingCoherentKleisli :
    @LocallyNameless.Categorical.TypingCoherent τ _ _ ν _ Φ _ (Type v)
      (Kleisli (CategoryTheory.ofTypeMonad m)) _ _ _ _ _ _ _ _ _ _ _ _
      (kleisliJ m) _ (Categorical.ofTypeModel (τ := τ))
      (Categorical.ofInstructionModel (ε := ε)) :=
  letI := Categorical.ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  { denote_eq := fun h k =>
      denoteOfType_ext (ε := ε) h k (exactDenote_coh (ε := ε) h k) }

/-- Coherence in the form used below: the categorical denotation of an exact
derivation depends only on the term and its type. -/
theorem denoteOfType_coh {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h k : HasType Φ Γ β t A) :
    Categorical.denoteOfType (ε := ε) (m := m) h.toGeneric =
      Categorical.denoteOfType (ε := ε) (m := m) k.toGeneric :=
  denoteOfType_ext (ε := ε) h k (exactDenote_coh (ε := ε) h k)

/-- Evaluating the categorical denotation at an embedded environment gives the
direct denotation.  This is `categorical_denote_eq` at an exact derivation. -/
theorem denoteOfType_apply {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) (γ : CtxDen Γ)
    (ρ : BoundDen β) :
    (Categorical.denoteOfType (ε := ε) (m := m) h.toGeneric).of
        (envToCategorical γ ρ) = exactDenote (ε := ε) (m := m) h γ ρ :=
  categorical_denote_eq (ε := ε) (m := m) h.toGeneric γ ρ

/-- The converse of `denoteOfType_ext`: equal categorical denotations have
equal direct denotations. -/
theorem denoteOfType_pointwise {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t t' : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A}
    {k : HasType Φ Γ β t' A}
    (H : Categorical.denoteOfType (ε := ε) (m := m) h.toGeneric =
      Categorical.denoteOfType (ε := ε) (m := m) k.toGeneric)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) h γ ρ =
      exactDenote (ε := ε) (m := m) k γ ρ := by
  rw [← denoteOfType_apply (ε := ε) h γ ρ, ← denoteOfType_apply (ε := ε) k γ ρ,
    H]

/-- **The lawful-model conditions hold at the Kleisli model.**  The first
instance of `Categorical.LawfulModel` anywhere in the development. -/
noncomputable instance instLawfulModelKleisli :
    @LocallyNameless.Categorical.LawfulModel τ _ _ ν _ Φ _ ε _ (⊥ : ε)
      (Type v) (Kleisli (CategoryTheory.ofTypeMonad m)) _ _ _ _ _ _ _ _ _ _ _ _
      (kleisliJ m) _ (Categorical.ofTypeModel (τ := τ))
      (Categorical.ofInstructionModel (ε := ε)) := by
  letI := Categorical.ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun hax ha hb =>
      denoteOfType_ext (ε := ε) ha hb
        (fun γ ρ => sound_ax (.structural hax) ha hb γ ρ)
  · exact fun hax ha hb =>
      denoteOfType_ext (ε := ε) ha hb
        (fun γ ρ => sound_ax (.sequencing hax) ha hb γ ρ)
  · exact fun hax ha hb =>
      denoteOfType_ext (ε := ε) ha hb
        (fun γ ρ => sound_ax (.iteration hax) ha hb γ ρ)
  · intro Γ n β a h b b' A A' B ha hh hp hb hb' square squareSound
    have hsq : ∀ (γ' : CtxDen Γ) (ρA : BoundDen (BoundCtx.snoc β A)),
        exactDenote (ε := ε) (m := m)
            (.case hb (.inl HasType.newest) (.inr hh.underBinder)) γ' ρA =
          exactDenote (ε := ε) (m := m)
            ((hb'.underBinder).instantiate hh) γ' ρA := by
      intro γ' ρA
      refine denoteOfType_pointwise (ε := ε) ?_ γ' ρA
      exact (denoteOfType_coh (ε := ε) _ square.leftTyping).trans
        (squareSound.trans (denoteOfType_coh (ε := ε) square.rightTyping _))
    exact denoteOfType_ext (ε := ε) (.iter ha hb) (.iter (.let₁ ha hh) hb')
      (fun γ ρ => sound_iterUniformity ha hh hp hb hb' hsq γ ρ)

/-- **Categorical soundness at the Kleisli model.**  This is
`LocallyNameless.Categorical.sound_between`, whose two class hypotheses are now
discharged, so the categorical semantics validates the whole equational theory
of lambda-iter at arbitrary endpoint derivations. -/
theorem kleisli_sound_between {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ}
    (e : Eqv (τ := τ) (ν := ν) (Φ := Φ) (ε := ε) (⊥ : ε) Γ β a b A)
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
    Categorical.denoteOfType (ε := ε) (m := m) ha.toGeneric =
      Categorical.denoteOfType (ε := ε) (m := m) hb.toGeneric :=
  @LocallyNameless.Categorical.sound_between τ _ _ ν _ Φ _ ε _ (⊥ : ε)
    (Type v) (Kleisli (CategoryTheory.ofTypeMonad m)) _ _ _ _ _ _ _ _ _ _ _ _
    (kleisliJ m) _ (Categorical.ofTypeModel (τ := τ))
    (Categorical.ofInstructionModel (ε := ε))
    instTypingCoherentKleisli instLawfulModelKleisli Γ n β a b A e ha hb

end Coherent

end Isotope.LambdaIter.Semantics
