import Isotope.TAC.Densem.MonadicConvertCFG
import Isotope.TAC.Densem.ConvertCFG

/-! # Iteration boundary square for monadic TAC-to-SSA conversion -/

namespace Isotope.TAC.Densem.Convert.Monadic

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert

variable {ν κ φ : Type} {m : Type → Type}
variable (M : Isotope.TAC.Densem.Monadic.Model φ m)

/-- The source-side loop body, stated directly on classical TAC blocks.  This
avoids imposing a vacuous empty-phi proof on the source representation. -/
def sourceStep [Monad m] [DecidableEq ν] [DecidableEq κ]
    (source : Isotope.TAC.Classical.CFG ν φ κ) :
    MEnv M ν × κ → m (M.Val ⊕ (MEnv M ν × κ))
  | (ρ, label) => match Isotope.TAC.Densem.Phi.lookup source label with
      | none => M.fail
      | some block => do
          let (ρ', exit) ← Isotope.TAC.Densem.Monadic.Block.denote M ρ
            (Isotope.TAC.Densem.Classical.block block)
          match exit with
          | .return a => pure (.inl a)
          | .branch next => pure (.inr (ρ', next))

/-- Observe a converted step at the reaching-version environment of the block
which has just executed.  This is the result map in the Elgot-uniformity
square; the predecessor component retained by phi semantics is erased. -/
def observeResult [DecidableEq ν]
    (label : κ) (block : Isotope.TAC.Classical.Block ν φ κ) :
    M.Val ⊕ (MEnv M (Version ν κ) × BlockId κ × κ) →
      M.Val ⊕ (MEnv M ν × κ) :=
  Sum.map id fun next =>
    (project (M := M) (endEnv (.named label) block) next.1, next.2.2)

/-- The finite observation of a converted loop result.  Conversion is
insensitive to variables outside `sourceVars`; retaining only this interface
is therefore the appropriate carrier for the store quotient. -/
def observeResultOn [DecidableEq ν]
    (vars : List ν) (label : κ)
    (block : Isotope.TAC.Classical.Block ν φ κ) :
    M.Val ⊕ (MEnv M (Version ν κ) × BlockId κ × κ) →
      M.Val ⊕ (MEnv M ν × κ) :=
  Sum.map id fun next =>
    (restrict M vars
      (project (M := M) (endEnv (.named label) block) next.1), next.2.2)

/-- Source iteration with its store quotiented to the finite compiler
interface after every successful block. -/
def sourceStepOn [Monad m] [DecidableEq ν] [DecidableEq κ]
    (source : Isotope.TAC.Classical.CFG ν φ κ) :
    MEnv M ν × κ → m (M.Val ⊕ (MEnv M ν × κ))
  | (ρ, label) => match Isotope.TAC.Densem.Phi.lookup source label with
      | none => M.fail
      | some block => do
          let (ρ', exit) ← Isotope.TAC.Densem.Monadic.Block.denote M ρ
            (Isotope.TAC.Densem.Classical.block block)
          match exit with
          | .return a => pure (.inl a)
          | .branch next =>
              pure (.inr (restrict M (sourceVars source) ρ', next))

private theorem restrict_idem [DecidableEq ν] (vars : List ν)
    (source : MEnv M ν) :
    restrict M vars (restrict M vars source) = restrict M vars source := by
  funext x
  by_cases hx : x ∈ vars <;> simp [restrict, hx]

/-- Exact loop-boundary square on the finite store interface.  Unlike
`step_denote`, this theorem makes no finiteness/exhaustiveness assumption on
the ambient variable type.  It is the representative-independence lemma used
to define the converted step on the observational store quotient. -/
theorem step_denote_restrict [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (sourceCfg : Isotope.TAC.Classical.CFG ν φ κ)
    (label : κ) (pred : BlockId κ)
    (predBlock block : Isotope.TAC.Classical.Block ν φ κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hlookup : Isotope.TAC.Densem.Phi.lookup sourceCfg label = some block)
    (hblock : (label, block) ∈ sourceCfg.blocks)
    (hpred : pred ∈ predecessors sourceCfg (.named label))
    (hpredBlock : sourceCfg.lookup pred = some predBlock)
    (htotal : TotalOn (M := M) (sourceVars sourceCfg) source)
    (hrel : EnvRelOn (M := M) (sourceVars sourceCfg)
      (endEnv pred predBlock) source target) :
    (Isotope.TAC.Densem.Phi.Monadic.step M
        (Isotope.TAC.Classical.Convert.convert sourceCfg)
        (target, pred, label) >>= fun result =>
      pure (observeResultOn M (sourceVars sourceCfg) label block result)) =
      sourceStepOn M sourceCfg (source, label) := by
  simp only [Isotope.TAC.Densem.Phi.Monadic.step, sourceStepOn]
  have hl := Isotope.TAC.Densem.Convert.lookup_convert sourceCfg label
  simp only [hl, hlookup, Option.map_some]
  let finish : MEnv M ν × Isotope.TAC.Densem.Exit κ M.Val →
      m (M.Val ⊕ (MEnv M ν × κ)) := fun result => match result.2 with
    | .return a => pure (Sum.inl a)
    | .branch next =>
        pure (Sum.inr (restrict M (sourceVars sourceCfg) result.1, next))
  have he := enter_named_denote_restrict M sourceCfg label pred predBlock block
    source target hblock hpred hpredBlock htotal hrel
  calc
    _ = ((Isotope.TAC.Densem.Phi.Monadic.enter M target pred
          (convertBlock sourceCfg (sourceVars sourceCfg) (.named label) block) >>=
        fun result => pure
          (restrict M (sourceVars sourceCfg)
            (project (M := M) (endEnv (.named label) block) result.1), result.2)) >>=
        finish) := by
          simp only [bind_assoc]
          apply congrArg (fun k =>
            Isotope.TAC.Densem.Phi.Monadic.enter M target pred
              (convertBlock sourceCfg (sourceVars sourceCfg) (.named label) block) >>= k)
          funext result
          rcases result with ⟨rho, exit⟩
          cases exit <;> simp [finish, observeResultOn, restrict_idem]
    _ = (Isotope.TAC.Densem.Monadic.Block.denote M source
          (Isotope.TAC.Densem.Classical.block block) >>= fun result =>
        pure (restrict M (sourceVars sourceCfg) result.1, result.2)) >>= finish :=
      congrArg (fun z => z >>= finish) he
    _ = _ := by
      simp only [bind_assoc]
      apply congrArg (fun k => Isotope.TAC.Densem.Monadic.Block.denote M source
        (Isotope.TAC.Densem.Classical.block block) >>= k)
      funext result
      rcases result with ⟨rho, exit⟩
      cases exit <;> simp [finish, restrict_idem]

/-- Converted stepping is independent of the representative of a versioned
store once both representatives agree with the same finite source-store
observation at the incoming boundary.  This is the well-definedness theorem
required by the observational quotient construction. -/
theorem step_observation_congr [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (sourceCfg : Isotope.TAC.Classical.CFG ν φ κ)
    (label : κ) (pred : BlockId κ)
    (predBlock block : Isotope.TAC.Classical.Block ν φ κ)
    (source : MEnv M ν) (left right : MEnv M (Version ν κ))
    (hlookup : Isotope.TAC.Densem.Phi.lookup sourceCfg label = some block)
    (hblock : (label, block) ∈ sourceCfg.blocks)
    (hpred : pred ∈ predecessors sourceCfg (.named label))
    (hpredBlock : sourceCfg.lookup pred = some predBlock)
    (htotal : TotalOn (M := M) (sourceVars sourceCfg) source)
    (hleft : EnvRelOn (M := M) (sourceVars sourceCfg)
      (endEnv pred predBlock) source left)
    (hright : EnvRelOn (M := M) (sourceVars sourceCfg)
      (endEnv pred predBlock) source right) :
    (Isotope.TAC.Densem.Phi.Monadic.step M
        (Isotope.TAC.Classical.Convert.convert sourceCfg)
        (left, pred, label) >>= fun result =>
      pure (observeResultOn M (sourceVars sourceCfg) label block result)) =
    (Isotope.TAC.Densem.Phi.Monadic.step M
        (Isotope.TAC.Classical.Convert.convert sourceCfg)
        (right, pred, label) >>= fun result =>
      pure (observeResultOn M (sourceVars sourceCfg) label block result)) := by
  rw [step_denote_restrict M sourceCfg label pred predBlock block source left
      hlookup hblock hpred hpredBlock htotal hleft,
    step_denote_restrict M sourceCfg label pred predBlock block source right
      hlookup hblock hpred hpredBlock htotal hright]

/-- Exact effectful commuting square for one reachable loop boundary.

The hypotheses are precisely the boundary invariant established by entry
conversion and preserved by successful converted blocks.  Consequently this
theorem is suitable for lifting through complete-Elgot iteration once loop
states are quotiented by the scoped environment relation (or represented by a
proof-relevant reachable-boundary type). -/
theorem step_denote [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (sourceCfg : Isotope.TAC.Classical.CFG ν φ κ)
    (label : κ) (pred : BlockId κ)
    (predBlock block : Isotope.TAC.Classical.Block ν φ κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hlookup : Isotope.TAC.Densem.Phi.lookup sourceCfg label = some block)
    (hpred : pred ∈ predecessors sourceCfg (.named label))
    (hpredBlock : sourceCfg.lookup pred = some predBlock)
    (htotal : Total (M := M) source)
    (hrel : EnvRelOn (M := M) (sourceVars sourceCfg)
      (endEnv pred predBlock) source target)
    (hcoverage : ∀ x, x ∈ sourceVars sourceCfg) :
    (Isotope.TAC.Densem.Phi.Monadic.step M
        (Isotope.TAC.Classical.Convert.convert sourceCfg)
        (target, pred, label) >>= fun result =>
      pure (observeResult M label block result)) =
      sourceStep M sourceCfg (source, label) := by
  simp only [Isotope.TAC.Densem.Phi.Monadic.step, sourceStep]
  have hl := Isotope.TAC.Densem.Convert.lookup_convert sourceCfg label
  simp only [hl, hlookup, Option.map_some]
  let finish : MEnv M ν × Isotope.TAC.Densem.Exit κ M.Val →
      m (M.Val ⊕ (MEnv M ν × κ)) := fun result => match result.2 with
    | .return a => pure (Sum.inl a)
    | .branch next => pure (Sum.inr (result.1, next))
  have he := enter_named_denote M sourceCfg label pred predBlock block source target
    hpred hpredBlock htotal hrel hcoverage
  calc
    _ = ((Isotope.TAC.Densem.Phi.Monadic.enter M target pred
          (convertBlock sourceCfg (sourceVars sourceCfg) (.named label) block) >>=
        fun result => pure
          (project (M := M) (endEnv (.named label) block) result.1, result.2)) >>=
        finish) := by
          simp only [bind_assoc]
          apply congrArg (fun k =>
            Isotope.TAC.Densem.Phi.Monadic.enter M target pred
              (convertBlock sourceCfg (sourceVars sourceCfg) (.named label) block) >>= k)
          funext result
          rcases result with ⟨rho, exit⟩
          cases exit <;> simp [finish, observeResult]
    _ = Isotope.TAC.Densem.Monadic.Block.denote M source
          (Isotope.TAC.Densem.Classical.block block) >>= finish :=
      congrArg (fun z => z >>= finish) he
    _ = _ := by rfl

end Isotope.TAC.Densem.Convert.Monadic
