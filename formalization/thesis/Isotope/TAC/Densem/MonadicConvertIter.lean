import Isotope.TAC.Densem.MonadicConvertCFG
import Isotope.TAC.Densem.ConvertCFG
import Isotope.TAC.Densem.MonadicClassical

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

/-- Project a raw converted store at a predecessor boundary.  The external
projection in the missing-predecessor case is intentional: guarded stepping
rejects that case whenever phis are present, while a program with no source
variables has no phis and cannot observe which projection was selected. -/
def projectBoundary [DecidableEq ν] [DecidableEq κ]
    (source : Isotope.TAC.Classical.CFG ν φ κ)
    (pred : BlockId κ) (target : MEnv M (Version ν κ)) : MEnv M ν :=
  match source.lookup pred with
  | some block => project (M := M) (endEnv pred block) target
  | none => fun x => target (.external x)

/-- Finite, executable recognition of store totality on the compiler
interface.  It requires no equality on semantic values. -/
def allPresent (vars : List ν) (source : MEnv M ν) : Bool :=
  vars.all fun x => (source x).isSome

theorem allPresent_eq_true_iff (vars : List ν) (source : MEnv M ν) :
    allPresent M vars source = true ↔ TotalOn (M := M) vars source := by
  rw [show allPresent M vars source =
    vars.all (fun x => (source x).isSome) from rfl, List.all_eq_true]
  constructor
  · intro h x hx
    exact Option.isSome_iff_exists.mp (h x hx)
  · intro h x hx
    exact Option.isSome_iff_exists.mpr (h x hx)

/-- Canonical phi installation fails as soon as one variable in its finite
interface is absent at the predecessor boundary. -/
theorem assignments_convert_missing [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    [Isotope.TAC.Densem.Phi.Monadic.LawfulFailure M]
    (source : Isotope.TAC.Classical.CFG ν φ κ) (vars : List ν)
    (label : κ) (pred : BlockId κ)
    (predBlock : Isotope.TAC.Classical.Block ν φ κ)
    (target : MEnv M (Version ν κ))
    (hpred : pred ∈ predecessors source (.named label))
    (hpredBlock : source.lookup pred = some predBlock)
    (hmissing : ∃ x ∈ vars, target (endEnv pred predBlock x) = none) :
    Isotope.TAC.Densem.Phi.Monadic.assignments M target pred
      (phis source vars label) = M.fail := by
  induction vars with
  | nil => simp at hmissing
  | cons x xs ih =>
      simp only [phis, List.map_cons,
        Isotope.TAC.Densem.Phi.Monadic.assignments]
      rw [incoming_select source (.named label) pred x predBlock hpred hpredBlock]
      simp only [Isotope.TAC.Densem.Classical.value,
        Isotope.TAC.Densem.Monadic.Value.denote]
      rcases hmissing with ⟨y, hy, hnone⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hnone]
        exact Isotope.TAC.Densem.Phi.Monadic.LawfulFailure.fail_bind _
      · cases hv : target (endEnv pred predBlock x) with
        | none =>
            exact Isotope.TAC.Densem.Phi.Monadic.LawfulFailure.fail_bind _
        | some a =>
            simp only [pure_bind]
            change (do
              let tail ← Isotope.TAC.Densem.Phi.Monadic.assignments M target pred
                (phis source xs label)
              pure ((Version.phi label x, a) :: tail)) = M.fail
            rw [ih ⟨y, hy, hnone⟩]
            exact Isotope.TAC.Densem.Phi.Monadic.LawfulFailure.fail_bind _

private theorem incoming_eq_none_of_not_mem [DecidableEq ν] [DecidableEq κ]
    (source : Isotope.TAC.Classical.CFG ν φ κ)
    (bid pred : BlockId κ) (x : ν)
    (hnot : pred ∉ predecessors source bid) :
    Isotope.TAC.Densem.Phi.incoming pred
      (incoming source bid x) = none := by
  unfold incoming Isotope.TAC.Densem.Phi.incoming
  generalize predecessors source bid = ps at hnot ⊢
  induction ps with
  | nil => rfl
  | cons q qs ih =>
      simp only [List.mem_cons, not_or] at hnot
      simp only [List.filterMap_cons]
      cases hq : blockAt source q with
      | none => simpa [hq] using ih hnot.2
      | some b =>
          simp only [hq, Option.map_some, List.find?_cons]
          have hne : q ≠ pred := fun h => hnot.1 h.symm
          simp only [hne, decide_false, if_false]
          exact ih hnot.2

/-- With a nonempty canonical phi interface, an invalid predecessor makes
phi assignment fail before the block body runs. -/
theorem assignments_convert_badPred [Monad m]
    [DecidableEq ν] [DecidableEq κ]
    (source : Isotope.TAC.Classical.CFG ν φ κ)
    (x : ν) (xs : List ν) (label : κ) (pred : BlockId κ)
    (target : MEnv M (Version ν κ))
    (hnot : pred ∉ predecessors source (.named label)) :
    Isotope.TAC.Densem.Phi.Monadic.assignments M target pred
      (phis source (x :: xs) label) = M.fail := by
  simp only [phis, List.map_cons,
    Isotope.TAC.Densem.Phi.Monadic.assignments]
  rw [incoming_eq_none_of_not_mem source (.named label) pred x hnot]

/-- Source loop state retaining predecessor control solely so that the
globally guarded body can reject exactly the malformed boundaries rejected by
converted phi installation. -/
abbrev GuardedState (M : Isotope.TAC.Densem.Monadic.Model φ m) (ν κ : Type) :=
  MEnv M ν × BlockId κ × κ

/-- Global comparison map proposed for Elgot uniformity. -/
def observeState [DecidableEq ν] [DecidableEq κ]
    (source : Isotope.TAC.Classical.CFG ν φ κ) :
    MEnv M (Version ν κ) × BlockId κ × κ → GuardedState M ν κ
  | (target, pred, label) => (projectBoundary M source pred target, pred, label)

/-- Globally defined source body used on the right of the Elgot-uniformity
square.  It accepts precisely the boundary shapes on which canonical phis can
run: all interface values must be present, and a nonempty phi interface also
requires a genuine predecessor edge.  With an empty interface there are no
phis, so the predecessor is deliberately ignored. -/
def guardedSourceStep [Monad m] [DecidableEq ν] [DecidableEq κ]
    (source : Isotope.TAC.Classical.CFG ν φ κ) :
    GuardedState M ν κ → m (M.Val ⊕ GuardedState M ν κ)
  | (ρ, pred, label) => match Isotope.TAC.Densem.Phi.lookup source label with
      | none => M.fail
      | some block =>
          if _htotal : allPresent M (sourceVars source) ρ = true then
            let run := do
              let (ρ', exit) ← Isotope.TAC.Densem.Monadic.Block.denote M ρ
                (Isotope.TAC.Densem.Classical.block block)
              match exit with
              | .return a => pure (.inl a)
              | .branch next => pure (.inr
                  (restrict M (sourceVars source) ρ', .named label, next))
            match sourceVars source with
            | [] => run
            | _ :: _ => match source.lookup pred with
                | none => M.fail
                | some _ => if pred ∈ predecessors source (.named label) then run
                  else M.fail
          else M.fail

/-- Observe the recursive predecessor as well as the finite source store. -/
def observeGuardedResult [DecidableEq ν]
    (vars : List ν) (label : κ)
    (block : Isotope.TAC.Classical.Block ν φ κ) :
    M.Val ⊕ (MEnv M (Version ν κ) × BlockId κ × κ) →
      M.Val ⊕ GuardedState M ν κ :=
  Sum.map id fun next =>
    (restrict M vars
      (project (M := M) (endEnv (.named label) block) next.1),
      .named label, next.2.2)

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

/-- On every valid finite-total boundary, the converted body commutes with
the globally guarded source body and retains the predecessor needed by the
next phi installation. -/
theorem step_denote_guarded_valid [Monad m] [LawfulMonad m]
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
      pure (observeGuardedResult M (sourceVars sourceCfg) label block result)) =
      guardedSourceStep M sourceCfg (source, pred, label) := by
  let addPred : M.Val ⊕ (MEnv M ν × κ) →
      M.Val ⊕ GuardedState M ν κ :=
    Sum.map id fun next => (next.1, .named label, next.2)
  have hs := step_denote_restrict M sourceCfg label pred predBlock block source target
    hlookup hblock hpred hpredBlock htotal hrel
  have hpresent : allPresent M (sourceVars sourceCfg) source = true :=
    (allPresent_eq_true_iff M _ _).2 htotal
  calc
    _ = ((Isotope.TAC.Densem.Phi.Monadic.step M
          (Isotope.TAC.Classical.Convert.convert sourceCfg)
          (target, pred, label) >>= fun result =>
        pure (observeResultOn M (sourceVars sourceCfg) label block result)) >>=
        fun result => pure (addPred result)) := by
          simp only [bind_assoc]
          apply congrArg (fun k => Isotope.TAC.Densem.Phi.Monadic.step M
            (Isotope.TAC.Classical.Convert.convert sourceCfg)
            (target, pred, label) >>= k)
          funext result
          cases result <;> simp [observeResultOn, observeGuardedResult, addPred]
    _ = sourceStepOn M sourceCfg (source, label) >>= fun result =>
          pure (addPred result) := congrArg (fun z => z >>= fun result =>
            pure (addPred result)) hs
    _ = _ := by
      simp only [sourceStepOn, hlookup, guardedSourceStep, hpresent,
        hpredBlock]
      cases hv : sourceVars sourceCfg <;> simp only [hv, hpred, if_pos]
      all_goals
        rw [dif_pos (by trivial)]
        simp only [bind_assoc, pure_bind]
        apply congrArg (fun k => Isotope.TAC.Densem.Monadic.Block.denote M source
          (Isotope.TAC.Densem.Classical.block block) >>= k)
        funext result
        rcases result with ⟨rho, exit⟩
        cases exit <;> simp [addPred]

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
