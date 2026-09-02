import Isotope.LambdaSSA.Semantics.Agreement.Region

/-! # Agreement of the chosen direct lambda-SSA denotations -/

namespace Isotope.LambdaSSA.Semantics

open CategoryTheory Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

namespace Agreement

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

private abbrev J := Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)
private noncomputable abbrev M := Categorical.ofTypeModel (τ := τ)

noncomputable def TermCoherent : Prop :=
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.TypingCoherent (Φ := Φ) (J (m := m)) (M (τ := τ))

noncomputable def RegionCoherent : Prop :=
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.RegionTypingCoherent (Φ := Φ) (J (m := m)) (M (τ := τ))

/-- The chosen categorical term denotation, specialized directly to the
Kleisli model induced by the monadic interpretation. -/
noncomputable def categoricalTermDenote {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) :=
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.denote (J (m := m)) (M (τ := τ)) h

omit [Iterate m] [LawfulElgotMonad m] in
/-- The chosen categorical and direct monadic term denotations agree
pointwise.  Coherence is explicit because extrinsic instruction typing may
carry semantically relevant evidence. -/
theorem categoricalTermDenote_eq
    (coherent : TermCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} (h : Tm.HasType Γ t A)
    (ρ : Monadic.Env Γ) :
    (categoricalTermDenote (ε := ε) (m := m) h).of
        (envToCategorical ρ) =
      Monadic.denote (ε := ε) (m := m) h ρ := by
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  letI : Categorical.TypingCoherent (Φ := Φ)
      (J (m := m)) (M (τ := τ)) := by
    simpa [TermCoherent] using coherent
  rcases denotes_toCategorical
      (Monadic.denote_spec (ε := ε) (m := m) h) with ⟨F, dF, hF⟩
  have hchosen := Categorical.denote_eq (J (m := m)) (M (τ := τ)) dF
  rw [categoricalTermDenote, hchosen]
  exact congrFun hF ρ

/-- The chosen categorical region denotation, including recursive CFG
iteration, specialized directly to the Kleisli model. -/
noncomputable def categoricalRegionDenote {Γ : VCtx τ} {region : Region Φ}
    {L : LCtx τ} (h : Region.HasType Γ region L) :=
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.Region.denote (J (m := m)) (M (τ := τ)) h

/-- The chosen categorical and direct monadic region/CFG denotations agree
pointwise, including their complete-Elgot iteration clauses. -/
theorem categoricalRegionDenote_eq
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ region L) (ρ : Monadic.Env Γ) :
    (categoricalRegionDenote (ε := ε) (m := m) h).of
        (envToCategorical ρ) =
      Monadic.Region.denote (ε := ε) (m := m) h ρ := by
  letI := Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  letI : Categorical.RegionTypingCoherent (Φ := Φ)
      (J (m := m)) (M (τ := τ)) := by
    simpa [RegionCoherent] using coherent
  rcases regionDenotes_toCategorical
      (Monadic.Region.denote_spec (ε := ε) (m := m) h) with ⟨F, dF, hF⟩
  have hchosen := Categorical.RegionDenotes.eq_denote
    (J (m := m)) (M (τ := τ)) dF
  rw [categoricalRegionDenote, ← hchosen]
  exact congrFun hF ρ

end Agreement
end Isotope.LambdaSSA.Semantics
