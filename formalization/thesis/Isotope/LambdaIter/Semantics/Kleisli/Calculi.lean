import Isotope.LambdaIter.Semantics.Kleisli.Model
import Isotope.LambdaCase.Semantics.Categorical
import Isotope.LambdaSeq.Categorical

/-!
# What the lambda-iter instances give lambda-case and lambda-seq

Neither `LambdaCase` nor `LambdaSeq` declares a coherence class of its own:
`LambdaCase.Semantics.Categorical.denoteChosen_independent` and
`LambdaSeq.Semantics.Categorical.Chosen.denote_independent` both consume
lambda-iter's `Categorical.TypingCoherent`, which had no instance.  With the
Kleisli instance of `Kleisli/Model.lean` in hand, both become unconditional at
the Kleisli model: the chosen categorical denotation of a lambda-case or
lambda-seq derivation does not depend on which lambda-iter typing witness is
picked for its image.

The results live here rather than in the two calculi's own directories so that
nothing outside `Isotope/LambdaIter/Semantics/Kleisli/` has to change.
-/

namespace Isotope.LambdaIter.Semantics

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.Elgot
open CategoryTheory

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]
variable [InjectiveFormers τ]

/-- **Lambda-case at the Kleisli model.**  Any two lambda-iter typing witnesses
for the image of a lambda-case derivation denote the same Kleisli morphism, so
`LambdaCase.Semantics.Categorical.denoteChosen` is independent of the witness
the inclusion happens to produce. -/
theorem lambdaCase_denoteChosen_independent
    {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaCase.LocallyNameless.BoundCtx τ n}
    {t : LambdaCase.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaCase.LocallyNameless.HasType Φ Γ β t A)
    (k : LocallyNameless.HasType Φ Γ β
      (LambdaCase.LocallyNameless.Tm.embed t) A) :
    Categorical.denoteOfType (ε := ε) (m := m) k.toGeneric =
      Categorical.denoteOfType (ε := ε) (m := m) h.embed.toGeneric :=
  denoteOfType_coh (ε := ε) k h.embed

/-- **Lambda-seq at the Kleisli model.**  The same statement for lambda-seq. -/
theorem lambdaSeq_denote_independent
    {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaSeq.LocallyNameless.HasType Φ Γ β t A)
    (k : LocallyNameless.HasType Φ Γ β
      (LambdaSeq.LocallyNameless.Tm.embedIter t) A) :
    Categorical.denoteOfType (ε := ε) (m := m) k.toGeneric =
      Categorical.denoteOfType (ε := ε) (m := m) h.embedIter.toGeneric :=
  denoteOfType_coh (ε := ε) k h.embedIter

end Isotope.LambdaIter.Semantics
