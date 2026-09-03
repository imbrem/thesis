import Isotope.LambdaCase.Semantics
import Isotope.LambdaSeq.Semantics
import Isotope.LambdaCase.Semantics.Categorical
import Isotope.LambdaSeq.Categorical
import Isotope.LambdaIter.Subtyping.Semantics.Agreement.Full
import Isotope.LambdaSSA.Translation.Compile.Semantics
import Isotope.LambdaSSA.Translation.Frontend.LambdaCase
import Isotope.LambdaSSA.Translation.Frontend.LambdaSeq

/-! # Semantic correctness of the exact lambda-case and lambda-seq frontends -/

namespace Isotope.LambdaSSA.Translation.Frontend

open Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open CategoryTheory

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

private abbrev J :=
  Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m)
private noncomputable abbrev M :=
  Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel (τ := τ)

/-- Relation-level categorical preservation corresponding to a monadic SSA
denotation.  It does not require a typing-choice coherence assumption. -/
noncomputable def CategoricalPreservation
    {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region Φ} {L : LambdaSSA.LCtx τ}
    (h : LambdaSSA.Region.HasType Γ r L)
    (f : Env Γ → m (LabelValue L)) : Prop :=
  letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  ∃ F : (J (m := m)).obj
        (Isotope.LambdaSSA.Semantics.Categorical.ctxObj (M (τ := τ)) Γ) ⟶
      (J (m := m)).obj
        (Isotope.LambdaSSA.Semantics.Categorical.labelObj (M (τ := τ)) L),
    Isotope.LambdaSSA.Semantics.Categorical.RegionDenotes
      (J (m := m)) (M (τ := τ)) h F ∧
    (fun ρ : Env Γ => F.of
        (Isotope.LambdaSSA.Semantics.Agreement.envToCategorical ρ)) =
      (fun ρ : Env Γ => f ρ >>= fun x =>
        pure (LabelValue.categoricalEquiv L x))

theorem categoricalPreservation_of_monadic
    {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region Φ} {L : LambdaSSA.LCtx τ}
    {h : LambdaSSA.Region.HasType Γ r L} {f : Env Γ → m (LabelValue L)}
    (d : RegionDenotes ε h f) : CategoricalPreservation (ε := ε) (m := m) h f := by
  exact Isotope.LambdaSSA.Semantics.Agreement.regionDenotes_toCategorical d

/-- End-to-end categorical preservation against a chosen source categorical
evaluator, with the result routed to the compiler's sole continuation. -/
noncomputable def CategoricalSourcePreservation
    {Γ : LambdaSSA.VCtx τ} {region : LambdaSSA.Region Φ} {A : τ}
    (h : LambdaSSA.Region.HasType Γ region [A])
    (source : Env Γ → m (TyDen A)) : Prop :=
  CategoricalPreservation (ε := ε) (m := m) h (fun ρ =>
    source ρ >>= fun a => pure (labelInject 0
      (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a))

theorem categoricalSourcePreservation_of_monadic
    {Γ : LambdaSSA.VCtx τ} {region : LambdaSSA.Region Φ} {A : τ}
    {h : LambdaSSA.Region.HasType Γ region [A]}
    {source monadic : Env Γ → m (TyDen A)}
    (d : RegionDenotes ε h (fun ρ => monadic ρ >>= fun a => pure
      (labelInject 0 (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)))
    (agree : ∀ ρ, source ρ = monadic ρ) :
    CategoricalSourcePreservation (ε := ε) (m := m) h source := by
  unfold CategoricalSourcePreservation
  convert categoricalPreservation_of_monadic d using 1
  funext ρ
  rw [agree ρ]
  rfl

namespace Core

/-- The exact lambda-iter frontend preserves its independently defined
monadic denotation. -/
theorem compile_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    RegionDenotes ε (compile_hasType h) (fun ρ =>
      LambdaIter.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.envToBound ρ) >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  have d := Compile.compile_denotes (ε := ε) (m := m) h
    (L := [A]) (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At])
  simpa only [compile, compile_hasType,
    Compile.exact_denote_eq_generic] using d

theorem compile_categorical_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    CategoricalPreservation (ε := ε) (m := m) (compile_hasType h) (fun ρ =>
      LambdaIter.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.envToBound ρ) >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compile_denotes h)

theorem compile_categorical_source_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    CategoricalSourcePreservation (ε := ε) (m := m) (compile_hasType h)
      (fun ρ => (Isotope.LambdaIter.Subtyping.Semantics.Categorical.denoteOfType
        (ε := ε) (m := m) h.toGeneric).of
          (envToCategorical PUnit.unit (ANF.ToSSA.envToBound ρ))) := by
  apply categoricalSourcePreservation_of_monadic (compile_denotes h)
  intro ρ
  exact (Isotope.LambdaIter.Subtyping.Semantics.categorical_denote_eq
    (ε := ε) (m := m) h.toGeneric PUnit.unit
    (ANF.ToSSA.envToBound ρ)).trans
      (Compile.exact_denote_eq_generic h PUnit.unit
        (ANF.ToSSA.envToBound ρ)).symm

end Core

namespace Core.Named

variable {ν : Type w} [DecidableEq ν]

/-- Compiling an exactly typed closed named lambda-iter term preserves the
denotation assigned by the named-to-locally-nameless semantic bridge. -/
theorem compileTyped_denotes
    {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx ν τ) t A) :
    RegionDenotes ε (compileTyped_hasType h) (fun _ =>
      NamedToLocallyNameless.denoteClosedChosenMonadic
          (ε := ε) (m := m) h PUnit.unit >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  have d := Core.compile_denotes (ε := ε) (m := m) (closedTerm h).2
  simpa only [compileTyped, compileTyped_hasType, closedTerm,
    NamedToLocallyNameless.denoteClosedChosenMonadic,
    Closed.erase_denotes] using d

theorem compileTyped_categorical_denotes
    {t : LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : LambdaIter.Named.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx ν τ) t A) :
    CategoricalPreservation (ε := ε) (m := m) (compileTyped_hasType h) (fun _ =>
      NamedToLocallyNameless.denoteClosedChosenMonadic
          (ε := ε) (m := m) h PUnit.unit >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compileTyped_denotes h)

end Core.Named

namespace LambdaCase.LocallyNameless

/-- Compiling an exact locally nameless lambda-case term preserves its direct
monadic denotation. -/
theorem compile_denotes
    {β : Isotope.LambdaCase.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaCase.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    RegionDenotes ε (compile_hasType h) (fun ρ =>
      Isotope.LambdaCase.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.envToBound ρ) >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  have d := Core.compile_denotes (ε := ε) (m := m) h.embed
  simpa only [compile, compile_hasType,
    Isotope.LambdaCase.Semantics.denote_embed] using d

theorem compile_categorical_denotes
    {β : Isotope.LambdaCase.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaCase.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    CategoricalPreservation (ε := ε) (m := m) (compile_hasType h) (fun ρ =>
      Isotope.LambdaCase.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.envToBound ρ) >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compile_denotes h)

theorem compile_categorical_source_denotes
    {β : Isotope.LambdaCase.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaCase.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    CategoricalSourcePreservation (ε := ε) (m := m) (compile_hasType h)
      (fun ρ => (Isotope.LambdaIter.Subtyping.Semantics.Categorical.denoteOfType
        (ε := ε) (m := m) h.embed.toGeneric).of
          (envToCategorical PUnit.unit (ANF.ToSSA.envToBound ρ))) := by
  apply categoricalSourcePreservation_of_monadic (compile_denotes h)
  intro ρ
  exact (Isotope.LambdaIter.Subtyping.Semantics.categorical_denote_eq
    (ε := ε) (m := m) h.embed.toGeneric PUnit.unit
    (ANF.ToSSA.envToBound ρ)).trans
      ((Compile.exact_denote_eq_generic h.embed PUnit.unit
        (ANF.ToSSA.envToBound ρ)).symm.trans
          (Isotope.LambdaCase.Semantics.denote_embed h PUnit.unit
            (ANF.ToSSA.envToBound ρ)))

end LambdaCase.LocallyNameless

namespace LambdaCase.Named

variable {ν : Type w} [DecidableEq ν]

/-- Compiling an exactly typed closed named lambda-case term preserves the
denotation of its named-to-locally-nameless lambda-iter interpretation. -/
theorem compileTyped_denotes
    {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Named.HasType
      (LambdaIter.Ctx.nil : LambdaIter.Ctx ν τ) t A) :
    RegionDenotes ε (compileTyped_hasType h) (fun _ =>
      NamedToLocallyNameless.denoteClosedChosenMonadic
          (ε := ε) (m := m) h.embed PUnit.unit >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  have d := Core.compile_denotes (ε := ε) (m := m) (closedTerm h).2
  simpa only [compileTyped, compileTyped_hasType, closedTerm,
    NamedToLocallyNameless.denoteClosedChosenMonadic,
    Closed.erase_denotes] using d

theorem compileTyped_categorical_denotes
    {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Named.HasType
      (LambdaIter.Ctx.nil : LambdaIter.Ctx ν τ) t A) :
    CategoricalPreservation (ε := ε) (m := m) (compileTyped_hasType h) (fun _ =>
      NamedToLocallyNameless.denoteClosedChosenMonadic
          (ε := ε) (m := m) h.embed PUnit.unit >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compileTyped_denotes h)

end LambdaCase.Named

namespace LambdaSeq.LocallyNameless

/-- Compiling an exact locally nameless lambda-seq term preserves its direct
monadic denotation. -/
theorem compile_denotes
    {β : Isotope.LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaSeq.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaSeq.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    RegionDenotes ε (compile_hasType h) (fun ρ =>
      Isotope.LambdaSeq.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.envToBound ρ) >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  have d := Core.compile_denotes (ε := ε) (m := m) h.embedIter
  simpa only [compile, compile_hasType,
    Isotope.LambdaSeq.Semantics.denote_embedIter] using d

theorem compile_categorical_denotes
    {β : Isotope.LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaSeq.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaSeq.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    CategoricalPreservation (ε := ε) (m := m) (compile_hasType h) (fun ρ =>
      Isotope.LambdaSeq.Semantics.denote (ε := ε) (m := m)
          h PUnit.unit (ANF.ToSSA.envToBound ρ) >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compile_denotes h)

theorem compile_categorical_source_denotes
    {β : Isotope.LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaSeq.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaSeq.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    CategoricalSourcePreservation (ε := ε) (m := m) (compile_hasType h)
      (fun ρ => (Isotope.LambdaIter.Subtyping.Semantics.Categorical.denoteOfType
        (ε := ε) (m := m) h.embedIter.toGeneric).of
          (envToCategorical PUnit.unit (ANF.ToSSA.envToBound ρ))) := by
  apply categoricalSourcePreservation_of_monadic (compile_denotes h)
  intro ρ
  exact (Isotope.LambdaIter.Subtyping.Semantics.categorical_denote_eq
    (ε := ε) (m := m) h.embedIter.toGeneric
    PUnit.unit (ANF.ToSSA.envToBound ρ)).trans
      ((Compile.exact_denote_eq_generic h.embedIter PUnit.unit
        (ANF.ToSSA.envToBound ρ)).symm.trans
          (Isotope.LambdaSeq.Semantics.denote_embedIter h PUnit.unit
            (ANF.ToSSA.envToBound ρ)))

end LambdaSeq.LocallyNameless

namespace LambdaSeq.Named

variable {ν : Type w} [DecidableEq ν]

/-- Compiling an exactly typed closed named lambda-seq term preserves the
denotation of its named-to-locally-nameless lambda-iter interpretation. -/
theorem compileTyped_denotes
    {t : Isotope.LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaSeq.Named.HasType
      (LambdaIter.Ctx.nil : LambdaIter.Ctx ν τ) t A) :
    RegionDenotes ε (compileTyped_hasType h) (fun _ =>
      NamedToLocallyNameless.denoteClosedChosenMonadic
          (ε := ε) (m := m) h.embedCase.embed PUnit.unit >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) := by
  simpa only [compileTyped, compileTyped_hasType] using
    LambdaCase.Named.compileTyped_denotes (ε := ε) (m := m) h.embedCase

theorem compileTyped_categorical_denotes
    {t : Isotope.LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaSeq.Named.HasType
      (LambdaIter.Ctx.nil : LambdaIter.Ctx ν τ) t A) :
    CategoricalPreservation (ε := ε) (m := m) (compileTyped_hasType h) (fun _ =>
      NamedToLocallyNameless.denoteClosedChosenMonadic
          (ε := ε) (m := m) h.embedCase.embed PUnit.unit >>= fun a =>
        pure (labelInject (L := [A]) 0
          (show LambdaSSA.At [A] 0 A by simp [LambdaSSA.At]) a)) :=
  categoricalPreservation_of_monadic (compileTyped_denotes h)

end LambdaSeq.Named

end Isotope.LambdaSSA.Translation.Frontend
