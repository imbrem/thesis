import Isotope.LambdaSSA.Translation.Compile
import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborate
import Isotope.LambdaSSA.Translation.ANF.ToSSA.SemanticsIter
import Isotope.LambdaSSA.Semantics.Agreement.Full

/-! # Denotational correctness of the composed LambdaIter-to-SSA compiler -/

namespace Isotope.LambdaSSA.Translation.Compile

open Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open CategoryTheory

universe u v q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

private abbrev J :=
  Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)
private noncomputable abbrev M :=
  Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel (τ := τ)

/-- The independently defined exact evaluator agrees with the generic
evaluator on the coercion-free embedding. -/
theorem exact_denote_eq_generic
    {ν : Type*} [DecidableEq ν]
    {Γ : LambdaIter.Ctx ν τ} {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaIter.LocallyNameless.HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    LambdaIter.Semantics.denote (ε := ε) (m := m) h γ ρ =
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
        h.toGeneric γ ρ := by
  induction h with
  | fv | bv | unit =>
      simp only [LambdaIter.Semantics.denote,
        LambdaIter.LocallyNameless.HasType.toGeneric,
        Isotope.LambdaIter.Subtyping.Semantics.denote]
  | op h ih => simp only [LambdaIter.Semantics.denote,
      LambdaIter.LocallyNameless.HasType.toGeneric,
      Isotope.LambdaIter.Subtyping.Semantics.denote, ih]
  | let₁ ha hb iha ihb =>
      simp only [LambdaIter.Semantics.denote,
        LambdaIter.LocallyNameless.HasType.toGeneric,
        Isotope.LambdaIter.Subtyping.Semantics.denote, iha]
      apply bind_congr
      exact fun a => ihb (ρ, a)
  | pair ha hb iha ihb =>
      simp only [LambdaIter.Semantics.denote,
        LambdaIter.LocallyNameless.HasType.toGeneric,
        Isotope.LambdaIter.Subtyping.Semantics.denote, iha, ihb]
  | let₂ ha hb iha ihb =>
      simp only [LambdaIter.Semantics.denote,
        LambdaIter.LocallyNameless.HasType.toGeneric,
        Isotope.LambdaIter.Subtyping.Semantics.denote, iha]
      apply bind_congr
      intro ab
      exact ihb _
  | inl h ih | inr h ih | abort h ih =>
      simp only [LambdaIter.Semantics.denote,
        LambdaIter.LocallyNameless.HasType.toGeneric,
        Isotope.LambdaIter.Subtyping.Semantics.denote, ih]
  | case he hl hr ihe ihl ihr =>
      simp only [LambdaIter.Semantics.denote,
        LambdaIter.LocallyNameless.HasType.toGeneric,
        Isotope.LambdaIter.Subtyping.Semantics.denote, ihe]
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl a => exact ihl _
      | inr b => exact ihr _
  | iter ha hb iha ihb =>
      simp only [LambdaIter.Semantics.denote,
        LambdaIter.LocallyNameless.HasType.toGeneric,
        Isotope.LambdaIter.Subtyping.Semantics.denote, iha]
      apply bind_congr
      intro a
      congr 1
      funext x
      rw [ihb]

/-- The composed compiler preserves the direct monadic denotation of an exact
LambdaIter derivation.  The result is routed to the selected SSA continuation. -/
theorem compile_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A) :
    RegionDenotes ε (compile_hasType h hout) (fun ρ =>
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          h.toGeneric PUnit.unit (ANF.ToSSA.envToBound ρ) >>= fun a =>
        pure (labelInject result hout a)) := by
  have d := ANF.ToSSA.program_denotes (ε := ε) (m := m)
    (ANF.Elaboration.elaborate_hasType h) hout
  have heval (ρ : BoundDen β) :
      LambdaIter.Semantics.denote (ε := ε) (m := m)
          (ANF.Elaboration.elaborate_hasType h).toLambdaIter PUnit.unit ρ =
        Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          h.toGeneric PUnit.unit ρ := by
    rw [exact_denote_eq_generic,
      ← ANF.Elaboration.Direct.denoteProgram_toLambdaIter,
      ANF.Elaboration.Direct.denote_elaborate]
  have hresult : ANF.ToSSA.resultEval (ε := ε) (m := m)
      (ANF.Elaboration.elaborate_hasType h) hout = fun ρ =>
        Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
            h.toGeneric PUnit.unit (ANF.ToSSA.envToBound ρ) >>= fun a =>
          pure (labelInject result hout a) := by
    funext ρ
    unfold ANF.ToSSA.resultEval
    rw [heval]
  rw [hresult] at d
  simpa [compile] using d

/-- The same compiler correctness result in the independently defined
categorical SSA semantics.  This relational form needs no choice-coherence
assumption: it produces the categorical witness induced by `compile_denotes`. -/
theorem compile_categorical_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A) :
    letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    ∃ F : (J (m := m)).obj
          (Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ))
            (LambdaSSA.LocallyNameless.ToDeBruijn.context β)) ⟶
        (J (m := m)).obj
          (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) L),
      Isotope.LambdaSSA.Semantics.Categorical.RegionDenotes
        (J (m := m)) (M (τ := τ)) (compile_hasType h hout) F ∧
      (fun ρ : Env (LambdaSSA.LocallyNameless.ToDeBruijn.context β) => F.of
          (Isotope.LambdaSSA.Semantics.Agreement.envToCategorical ρ)) =
        (fun ρ : Env (LambdaSSA.LocallyNameless.ToDeBruijn.context β) =>
          (Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
              h.toGeneric PUnit.unit (ANF.ToSSA.envToBound ρ) >>= fun a =>
            pure (labelInject result hout a)) >>= fun x =>
              pure (LabelValue.categoricalEquiv L x)) := by
  exact Isotope.LambdaSSA.Semantics.Agreement.regionDenotes_toCategorical
    (compile_denotes (ε := ε) (m := m) h hout)

end Isotope.LambdaSSA.Translation.Compile
