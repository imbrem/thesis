import Isotope.LambdaSSA.Translation.Compile.Subtyping
import Isotope.LambdaSSA.Translation.ANF.Subtyping.SemanticsPreservation
import Isotope.LambdaSSA.Translation.ANF.ToSSA.Subtyping.SemanticsIter
import Isotope.LambdaSSA.Subtyping.Semantics.Agreement.Region

/-! # Proof-relevant denotational correctness of lambda-iter compilation -/

namespace Isotope.LambdaSSA.Translation.Compile.Subtyping

open Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaSSA.Subtyping.Semantics.Monadic
open CategoryTheory

universe u v q r

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
variable [TypeModel.{u, v} τ] [LawfulTypeModel τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

private abbrev J :=
  Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)
private noncomputable abbrev M :=
  Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel (τ := τ)

/-- The proof-relevant compiler preserves the direct monadic denotation,
including the particular coercions selected by its source derivation. -/
theorem compile_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaIter.Subtyping.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A) :
    RegionDenotes ε (compile_hasType h hout) (fun ρ =>
      LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.Subtyping.envToBound ρ) >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject result hout a)) := by
  have d := ANF.ToSSA.Subtyping.program_denotes (ε := ε) (m := m)
    (ANF.Subtyping.elaborate_hasType h) hout
  have hresult : ANF.ToSSA.Subtyping.resultEval (ε := ε) (m := m)
      (ANF.Subtyping.elaborate_hasType h) (Subty.refl A) hout =
      fun ρ => LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.Subtyping.envToBound ρ) >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject result hout a) := by
    funext ρ
    unfold ANF.ToSSA.Subtyping.resultEval
    rw [show coeSub (Subty.refl A) = id from LawfulTypeModel.coe_refl A]
    simp only [id_eq, LawfulMonad.pure_bind,
      ANF.Subtyping.denote_elaborate]
  rw [hresult] at d
  change RegionDenotes ε
    (ANF.ToSSA.Subtyping.program_hasType (ANF.Subtyping.elaborate_hasType h) hout) _
  exact d

/-- Categorical preservation is the proof-relevant SSA agreement image of
the direct monadic compiler theorem, so it adds no coherence assumption on
subtyping witnesses. -/
theorem compile_categorical_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaIter.Subtyping.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A) :
    letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    ∃ F : (J (m := m)).obj
          (Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ))
            (LambdaSSA.LocallyNameless.ToDeBruijn.context β)) ⟶
        (J (m := m)).obj
          (Isotope.LambdaSSA.Semantics.Categorical.labelObj
            (M (τ := τ)) L),
      Isotope.LambdaSSA.Subtyping.Semantics.Categorical.RegionDenotes
        (J (m := m)) (M (τ := τ)) (compile_hasType h hout) F ∧
      (fun ρ : Isotope.LambdaSSA.Semantics.Monadic.Env
          (LambdaSSA.LocallyNameless.ToDeBruijn.context β) => F.of
          (Isotope.LambdaSSA.Subtyping.Semantics.Agreement.envToCategorical ρ)) =
        (fun ρ =>
          (LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
              h PUnit.unit (ANF.ToSSA.Subtyping.envToBound ρ) >>= fun a =>
            pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject result hout a)) >>= fun x =>
              pure (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L x)) := by
  exact Isotope.LambdaSSA.Subtyping.Semantics.Agreement.regionDenotes_toCategorical
    (compile_denotes (ε := ε) (m := m) h hout)

end Isotope.LambdaSSA.Translation.Compile.Subtyping
