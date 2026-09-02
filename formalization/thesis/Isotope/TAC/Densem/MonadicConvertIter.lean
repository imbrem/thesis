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
