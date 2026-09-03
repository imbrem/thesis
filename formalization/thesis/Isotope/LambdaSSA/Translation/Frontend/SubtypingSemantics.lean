import Isotope.LambdaCase.Semantics
import Isotope.LambdaSeq.Semantics
import Isotope.LambdaCase.Subtyping.Semantics.Categorical
import Isotope.LambdaSeq.Categorical
import Isotope.LambdaIter.Subtyping.Semantics.NamedToLocallyNameless
import Isotope.LambdaSSA.Translation.Compile.Subtyping.Semantics
import Isotope.LambdaSSA.Translation.Frontend.Subtyping

/-! # Semantic correctness of the proof-relevant subtyping frontends -/

namespace Isotope.LambdaSSA.Translation.Frontend.Subtyping

open Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaSSA.Subtyping.Semantics.Monadic
open CategoryTheory

universe u v w q r

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

/-- Relation-level categorical preservation induced by a proof-relevant
monadic SSA denotation. -/
noncomputable def CategoricalPreservation
    {Γ : LambdaSSA.VCtx τ} {region : LambdaSSA.Region Φ} {L : LambdaSSA.LCtx τ}
    (h : LambdaSSA.Subtyping.Region.HasType Γ region L)
    (f : Isotope.LambdaSSA.Semantics.Monadic.Env Γ →
      m (Isotope.LambdaSSA.Semantics.Monadic.LabelValue L)) : Prop :=
  letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  ∃ F : (J (m := m)).obj
        (Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ)) Γ) ⟶
      (J (m := m)).obj
        (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) L),
    Isotope.LambdaSSA.Subtyping.Semantics.Categorical.RegionDenotes
      (J (m := m)) (M (τ := τ)) h F ∧
    (fun ρ => F.of
        (Isotope.LambdaSSA.Subtyping.Semantics.Agreement.envToCategorical ρ)) =
      (fun ρ => f ρ >>= fun x => pure
        (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L x))

theorem categoricalPreservation_of_monadic
    {Γ : LambdaSSA.VCtx τ} {region : LambdaSSA.Region Φ} {L : LambdaSSA.LCtx τ}
    {h : LambdaSSA.Subtyping.Region.HasType Γ region L}
    {f : Isotope.LambdaSSA.Semantics.Monadic.Env Γ →
      m (Isotope.LambdaSSA.Semantics.Monadic.LabelValue L)}
    (d : RegionDenotes ε h f) :
    CategoricalPreservation (ε := ε) (m := m) h f :=
  Isotope.LambdaSSA.Subtyping.Semantics.Agreement.regionDenotes_toCategorical d

/-- End-to-end categorical preservation against a source categorical
evaluator, including the compiler's result-label routing. -/
noncomputable def CategoricalSourcePreservation
    {Γ : LambdaSSA.VCtx τ} {region : LambdaSSA.Region Φ} {A : τ}
    (h : LambdaSSA.Subtyping.Region.HasType Γ region [A])
    (source : Isotope.LambdaSSA.Semantics.Monadic.Env Γ → m (TyDen A)) : Prop :=
  let hout : LambdaSSA.At [A] 0 A := by simp [LambdaSSA.At]
  letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  ∃ F : (J (m := m)).obj
        (Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ)) Γ) ⟶
      (J (m := m)).obj
        (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) [A]),
    Isotope.LambdaSSA.Subtyping.Semantics.Categorical.RegionDenotes
      (J (m := m)) (M (τ := τ)) h F ∧
    (fun ρ => F.of
        (Isotope.LambdaSSA.Subtyping.Semantics.Agreement.envToCategorical ρ)) =
      (fun ρ => (source ρ >>= fun a => pure
        (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0 hout a)) >>= fun x =>
          pure (Isotope.LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv [A] x))

theorem categoricalSourcePreservation_of_monadic
    {Γ : LambdaSSA.VCtx τ} {region : LambdaSSA.Region Φ} {A : τ}
    {h : LambdaSSA.Subtyping.Region.HasType Γ region [A]}
    {source monadic : Isotope.LambdaSSA.Semantics.Monadic.Env Γ → m (TyDen A)}
    (d : RegionDenotes ε h (fun ρ => monadic ρ >>= fun a => pure
      (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
        (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)))
    (agree : ∀ ρ, source ρ = monadic ρ) :
    CategoricalSourcePreservation (ε := ε) (m := m) h source := by
  rcases categoricalPreservation_of_monadic d with ⟨F, dF, eF⟩
  refine ⟨F, dF, ?_⟩
  funext ρ
  rw [congrFun eF ρ, agree ρ]
  rfl

namespace LambdaIter.LocallyNameless

theorem compile_denotes
    {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    RegionDenotes ε (compile_hasType h) (fun ρ =>
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.Subtyping.envToBound ρ) >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  simpa only [compile, compile_hasType] using
    Compile.Subtyping.compile_denotes (ε := ε) (m := m) h
      (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At])

theorem compile_categorical_denotes
    {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    CategoricalPreservation (ε := ε) (m := m) (compile_hasType h) (fun ρ =>
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.Subtyping.envToBound ρ) >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compile_denotes h)

theorem compile_categorical_source_denotes
    {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    CategoricalSourcePreservation (ε := ε) (m := m) (compile_hasType h)
      (fun ρ =>
        (Isotope.LambdaIter.Subtyping.Semantics.Categorical.denoteOfType
          (ε := ε) (m := m) h).of
            (Isotope.LambdaIter.Subtyping.Semantics.envToCategorical PUnit.unit
              (ANF.ToSSA.Subtyping.envToBound ρ))) := by
  letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  apply categoricalSourcePreservation_of_monadic (compile_denotes h)
  intro ρ
  exact Isotope.LambdaIter.Subtyping.Semantics.categorical_denote_eq h
    PUnit.unit (ANF.ToSSA.Subtyping.envToBound ρ)

end LambdaIter.LocallyNameless

namespace LambdaCase.LocallyNameless

theorem compile_denotes
    {β : Isotope.LambdaCase.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaCase.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    RegionDenotes ε (compile_hasType h) (fun ρ =>
      Isotope.LambdaCase.Subtyping.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.Subtyping.envToBound ρ) >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  have d := LambdaIter.LocallyNameless.compile_denotes
    (ε := ε) (m := m) h.embed
  simpa only [compile, compile_hasType,
    Isotope.LambdaCase.Subtyping.Semantics.denote_embed] using d

theorem compile_categorical_denotes
    {β : Isotope.LambdaCase.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaCase.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    CategoricalPreservation (ε := ε) (m := m) (compile_hasType h) (fun ρ =>
      Isotope.LambdaCase.Subtyping.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.Subtyping.envToBound ρ) >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compile_denotes h)

theorem compile_categorical_source_denotes
    {β : Isotope.LambdaCase.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaCase.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    CategoricalSourcePreservation (ε := ε) (m := m) (compile_hasType h)
      (fun ρ =>
        (Isotope.LambdaCase.Subtyping.Semantics.Categorical.denote
          (J (m := m)) (M (τ := τ)) h).of
            (Isotope.LambdaIter.Subtyping.Semantics.envToCategorical PUnit.unit
              (ANF.ToSSA.Subtyping.envToBound ρ))) := by
  letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  apply categoricalSourcePreservation_of_monadic (compile_denotes h)
  intro ρ
  rw [← Isotope.LambdaCase.Subtyping.Semantics.Categorical.denote_embed
    (J (m := m)) (M (τ := τ)) h]
  exact (Isotope.LambdaIter.Subtyping.Semantics.categorical_denote_eq
    (ε := ε) (m := m) h.embed PUnit.unit
      (ANF.ToSSA.Subtyping.envToBound ρ)).trans
        (Isotope.LambdaCase.Subtyping.Semantics.denote_embed h PUnit.unit
          (ANF.ToSSA.Subtyping.envToBound ρ))

end LambdaCase.LocallyNameless

namespace LambdaSeq.LocallyNameless

theorem compile_denotes
    {β : Isotope.LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaSeq.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaSeq.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    RegionDenotes ε (compile_hasType h) (fun ρ =>
      Isotope.LambdaSeq.Subtyping.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.Subtyping.envToBound ρ) >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  have d := LambdaIter.LocallyNameless.compile_denotes
    (ε := ε) (m := m) h.embedIter
  simpa only [compile, compile_hasType,
    Isotope.LambdaSeq.Subtyping.Semantics.denote_embedIter] using d

theorem compile_categorical_denotes
    {β : Isotope.LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaSeq.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaSeq.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    CategoricalPreservation (ε := ε) (m := m) (compile_hasType h) (fun ρ =>
      Isotope.LambdaSeq.Subtyping.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.Subtyping.envToBound ρ) >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compile_denotes h)

theorem compile_categorical_source_denotes
    {β : Isotope.LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaSeq.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaSeq.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    CategoricalSourcePreservation (ε := ε) (m := m) (compile_hasType h)
      (fun ρ =>
        (Isotope.LambdaSeq.Semantics.Categorical.transportSrc
          (congrArg (J (m := m)).obj
            (Isotope.LambdaSeq.Semantics.Categorical.envObjEq
              (M (τ := τ)) (Ctx.nil : Ctx Empty τ) β))
          (Isotope.LambdaSeq.Subtyping.Semantics.Categorical.denoteOfIter
            (J (m := m)) (M (τ := τ)) h)).of
              (Isotope.LambdaIter.Subtyping.Semantics.envToCategorical PUnit.unit
              (ANF.ToSSA.Subtyping.envToBound ρ))) := by
  letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  apply categoricalSourcePreservation_of_monadic (compile_denotes h)
  intro ρ
  rw [Isotope.LambdaSeq.Subtyping.Semantics.Categorical.denoteOfIter_transport_eq]
  exact (Isotope.LambdaIter.Subtyping.Semantics.categorical_denote_eq
    (ε := ε) (m := m) h.embedIter PUnit.unit
      (ANF.ToSSA.Subtyping.envToBound ρ)).trans
        (Isotope.LambdaSeq.Subtyping.Semantics.denote_embedIter h PUnit.unit
          (ANF.ToSSA.Subtyping.envToBound ρ))

end LambdaSeq.LocallyNameless

section Named

variable {ν : Type w} [DecidableEq ν]

private theorem denote_eraseClosed
    {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx ν τ) β t A)
    (ρ : Isotope.LambdaIter.Subtyping.Semantics.BoundDen β) :
    Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
        (Closed.Subtyping.erase h).2 PUnit.unit ρ =
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
        h PUnit.unit ρ := by
  induction h with
  | fv h => simp [Ctx.lookup] at h
  | bv | unit =>
      simp only [Closed.Subtyping.erase]
      unfold Isotope.LambdaIter.Subtyping.Semantics.denote
      rfl
  | op h ih | inl h ih | inr h ih | abort h ih | sub h _ ih =>
      simp only [Closed.Subtyping.erase]
      unfold Isotope.LambdaIter.Subtyping.Semantics.denote
      rw [ih]
  | let₁ ha hb iha ihb =>
      simp only [Closed.Subtyping.erase]
      unfold Isotope.LambdaIter.Subtyping.Semantics.denote
      rw [iha]
      apply bind_congr
      intro a
      exact ihb (ρ, a)
  | pair ha hb iha ihb =>
      simp only [Closed.Subtyping.erase]
      unfold Isotope.LambdaIter.Subtyping.Semantics.denote
      rw [iha, ihb]
  | let₂ ha hc iha ihc =>
      simp only [Closed.Subtyping.erase]
      unfold Isotope.LambdaIter.Subtyping.Semantics.denote
      rw [iha]
      apply bind_congr
      intro ab
      exact ihc ((ρ, (TypeModel.tensorEquiv _ _ ab).1),
        (TypeModel.tensorEquiv _ _ ab).2)
  | case he hl hr ihe ihl ihr =>
      simp only [Closed.Subtyping.erase]
      unfold Isotope.LambdaIter.Subtyping.Semantics.denote
      rw [ihe]
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl a => exact ihl (ρ, a)
      | inr b => exact ihr (ρ, b)
  | iter ha hb iha ihb =>
      simp only [Closed.Subtyping.erase]
      unfold Isotope.LambdaIter.Subtyping.Semantics.denote
      rw [iha]
      apply bind_congr
      intro a
      congr 1
      funext x
      rw [ihb (ρ, x)]

namespace LambdaIter.Named

/-- Compiling a closed named derivation preserves the monadic denotation of
the public, proof-relevant named-to-locally-nameless lowering selected by the
frontend. -/
theorem compileTyped_denotes
    {t : Isotope.LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    RegionDenotes ε (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          (lowerNamed h).2 PUnit.unit PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  simpa only [compileTyped, compileTyped_hasType] using
    LambdaIter.LocallyNameless.compile_denotes
      (ε := ε) (m := m) (lowerNamed h).2

/-- End-to-end preservation against the independent direct named evaluator. -/
theorem compileTyped_direct_denotes
    {t : Isotope.LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    RegionDenotes ε (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaIter.Subtyping.Semantics.Named.denote
          (ε := ε) (m := m) h PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  simpa only [lowerNamed, denote_eraseClosed,
    Isotope.LambdaIter.Subtyping.Semantics.denote_translateHasTypeClosed] using
    compileTyped_denotes (ε := ε) (m := m) h

theorem compileTyped_categorical_denotes
    {t : Isotope.LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    CategoricalPreservation (ε := ε) (m := m) (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          (lowerNamed h).2 PUnit.unit PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compileTyped_denotes h)

theorem compileTyped_direct_categorical_denotes
    {t : Isotope.LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    CategoricalPreservation (ε := ε) (m := m) (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaIter.Subtyping.Semantics.Named.denote
          (ε := ε) (m := m) h PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compileTyped_direct_denotes h)

end LambdaIter.Named

namespace LambdaCase.Named

theorem compileTyped_denotes
    {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    RegionDenotes ε (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          (lowerNamed h.embed).2 PUnit.unit PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  simpa only [compileTyped, compileTyped_hasType] using
    LambdaIter.Named.compileTyped_denotes (ε := ε) (m := m) h.embed

theorem compileTyped_direct_denotes
    {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    RegionDenotes ε (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaCase.Subtyping.Semantics.Named.denote
          (ε := ε) (m := m) h PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  simpa only [compileTyped, compileTyped_hasType,
    Isotope.LambdaCase.Subtyping.Semantics.Named.denote_embed] using
    LambdaIter.Named.compileTyped_direct_denotes
      (ε := ε) (m := m) h.embed

theorem compileTyped_categorical_denotes
    {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    CategoricalPreservation (ε := ε) (m := m) (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          (lowerNamed h.embed).2 PUnit.unit PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compileTyped_denotes h)

theorem compileTyped_direct_categorical_denotes
    {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    CategoricalPreservation (ε := ε) (m := m) (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaCase.Subtyping.Semantics.Named.denote
          (ε := ε) (m := m) h PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compileTyped_direct_denotes h)

end LambdaCase.Named

namespace LambdaSeq.Named

theorem compileTyped_denotes
    {t : Isotope.LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaSeq.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    RegionDenotes ε (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          (lowerNamed h.embedIter).2 PUnit.unit PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  simpa only [compileTyped, compileTyped_hasType] using
    LambdaIter.Named.compileTyped_denotes (ε := ε) (m := m) h.embedIter

theorem compileTyped_direct_denotes
    {t : Isotope.LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaSeq.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    RegionDenotes ε (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaSeq.Subtyping.Semantics.Named.denote
          (ε := ε) (m := m) h PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  simpa only [compileTyped, compileTyped_hasType,
    Isotope.LambdaSeq.Subtyping.Semantics.Named.denote_embedIter] using
    LambdaIter.Named.compileTyped_direct_denotes
      (ε := ε) (m := m) h.embedIter

theorem compileTyped_categorical_denotes
    {t : Isotope.LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaSeq.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    CategoricalPreservation (ε := ε) (m := m) (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaIter.Subtyping.Semantics.denote (ε := ε) (m := m)
          (lowerNamed h.embedIter).2 PUnit.unit PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compileTyped_denotes h)

theorem compileTyped_direct_categorical_denotes
    {t : Isotope.LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaSeq.Subtyping.Named.HasType
      (Ctx.nil : Ctx ν τ) t A) :
    CategoricalPreservation (ε := ε) (m := m) (compileTyped_hasType h) (fun _ =>
      Isotope.LambdaSeq.Subtyping.Semantics.Named.denote
          (ε := ε) (m := m) h PUnit.unit >>= fun a =>
        pure (Isotope.LambdaSSA.Semantics.Monadic.labelInject 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compileTyped_direct_denotes h)

end LambdaSeq.Named

end Named

end Isotope.LambdaSSA.Translation.Frontend.Subtyping
