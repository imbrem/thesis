import Isotope.TAC.Densem.MonadicConvertIter

/-! # Proof-carrying valid states for TAC iteration -/

namespace Isotope.TAC.Densem.Convert.Monadic.Valid

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert
open Isotope.TAC.Densem.Convert.Monadic

variable {ν κ φ : Type} {m : Type → Type}
variable (M : Isotope.TAC.Densem.Monadic.Model φ m)

structure Store (vars : List ν) where
  env : MEnv M ν
  total : TotalOn (M := M) vars env

def Store.set [DecidableEq ν] {vars : List ν} (s : Store M vars)
    (x : ν) (a : M.Val) : Store M vars where
  env := Isotope.TAC.Densem.Monadic.Env.set s.env x a
  total := by
    intro y hy
    by_cases h : y = x
    · subst y
      exact ⟨a, by simp [Isotope.TAC.Densem.Monadic.Env.set]⟩
    · rcases s.total y hy with ⟨b, hb⟩
      exact ⟨b, by simp [Isotope.TAC.Densem.Monadic.Env.set, h, hb]⟩

def CheckedExit (t : Isotope.TAC.Classical.Terminator ν φ κ) :=
  {e : Isotope.TAC.Densem.Exit κ M.Val //
    Isotope.TAC.Densem.Convert.ExitTargets t e}

def terminator [Monad m] {vars : List ν} (s : Store M vars) :
    (t : Isotope.TAC.Classical.Terminator ν φ κ) → m (CheckedExit M t)
  | .br label => pure ⟨.branch label, by simp [Isotope.TAC.Densem.Convert.ExitTargets,
      Isotope.TAC.Classical.Terminator.targets]⟩
  | .ret value => do
      let a ← Isotope.TAC.Densem.Monadic.Value.denote M s.env
        (Isotope.TAC.Densem.Classical.value (ν := ν) value)
      pure ⟨.return a, trivial⟩
  | .cond c left right => do
      let b ← Isotope.TAC.Densem.Monadic.Operand.denote M s.env
        (Isotope.TAC.Densem.Classical.operand (ν := ν) (φ := φ) c) >>= M.viewBool
      if b then
        let e ← terminator s left
        match e with
        | ⟨.return a, _⟩ => pure ⟨.return a, trivial⟩
        | ⟨.branch label, he⟩ =>
            pure ⟨.branch label, List.mem_append_left _ he⟩
      else
        let e ← terminator s right
        match e with
        | ⟨.return a, _⟩ => pure ⟨.return a, trivial⟩
        | ⟨.branch label, he⟩ =>
            pure ⟨.branch label, List.mem_append_right _ he⟩

theorem terminator_forget [Monad m] [LawfulMonad m] {vars : List ν}
    (s : Store M vars)
    (t : Isotope.TAC.Classical.Terminator ν φ κ) :
    (terminator M s t >>= fun e => pure e.1) =
      Isotope.TAC.Densem.Monadic.Terminator.denote M s.env
        (Isotope.TAC.Densem.Classical.terminator t) := by
  induction t with
  | br => simp [terminator, Isotope.TAC.Densem.Classical.terminator,
      Isotope.TAC.Densem.Monadic.Terminator.denote]
  | ret value =>
      simp [terminator, Isotope.TAC.Densem.Classical.terminator,
        Isotope.TAC.Densem.Monadic.Terminator.denote, bind_assoc]
  | cond c left right ihl ihr =>
      simp only [terminator, Isotope.TAC.Densem.Classical.terminator,
        Isotope.TAC.Densem.Monadic.Terminator.denote, bind_assoc]
      apply congrArg (fun k =>
        Isotope.TAC.Densem.Monadic.Operand.denote M s.env
          (Isotope.TAC.Densem.Classical.operand c) >>= k)
      funext a
      apply congrArg (fun k => M.viewBool a >>= k)
      funext b
      cases b with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          rw [← ihr]
          simp only [bind_assoc]
          apply congrArg (fun k => terminator M s right >>= k)
          funext e
          rcases e with ⟨e, he⟩
          cases e <;> simp
      | true =>
          simp only [if_true]
          rw [← ihl]
          simp only [bind_assoc]
          apply congrArg (fun k => terminator M s left >>= k)
          funext e
          rcases e with ⟨e, he⟩
          cases e <;> simp

def block [Monad m] [DecidableEq ν] {vars : List ν} (s : Store M vars)
    (xs : List (Isotope.TAC.Classical.Instr ν φ))
    (t : Isotope.TAC.Classical.Terminator ν φ κ) :
    m (Store M vars × CheckedExit M t) :=
  match xs with
  | [] => do
      let e ← terminator M s t
      pure (s, e)
  | .assign x rhs :: rest => do
      let a ← Isotope.TAC.Densem.Monadic.Operand.denote M s.env
        (Isotope.TAC.Densem.Classical.operand (ν := ν) (φ := φ) rhs)
      block (Store.set M s x a) rest t
  | .assignPair x y rhs :: rest => do
      let a ← Isotope.TAC.Densem.Monadic.Operand.denote M s.env
        (Isotope.TAC.Densem.Classical.operand (ν := ν) (φ := φ) rhs)
      let (ax, ay) ← M.split a
      block (Store.set M (Store.set M s x ax) y ay) rest t

theorem block_forget [Monad m] [LawfulMonad m] [DecidableEq ν]
    {vars : List ν} (s : Store M vars)
    (xs : List (Isotope.TAC.Classical.Instr ν φ))
    (t : Isotope.TAC.Classical.Terminator ν φ κ) :
    (block M s xs t >>= fun result => pure (result.1.env, result.2.1)) =
      Isotope.TAC.Densem.Monadic.Block.denote M s.env
        (Isotope.TAC.Densem.Classical.instructions xs
          (Isotope.TAC.Densem.Classical.terminator t)) := by
  induction xs generalizing s with
  | nil =>
      simp only [block, Isotope.TAC.Densem.Classical.instructions,
        Isotope.TAC.Densem.Monadic.Block.denote, bind_assoc, pure_bind,
        map_eq_pure_bind]
      have ht := terminator_forget M s t
      calc
        _ = terminator M s t >>= fun e =>
            pure e.1 >>= fun exit => pure (s.env, exit) := by
              apply congrArg (fun k => terminator M s t >>= k)
              funext e
              simp
        _ = (terminator M s t >>= fun e => pure e.1) >>= fun exit =>
            pure (s.env, exit) := (bind_assoc _ _ _).symm
        _ = _ := congrArg (fun z => z >>= fun exit => pure (s.env, exit)) ht
  | cons instr rest ih =>
      cases instr with
      | assign x rhs =>
          simp only [block, Isotope.TAC.Densem.Classical.instructions,
            Isotope.TAC.Densem.Monadic.Block.denote, bind_assoc]
          apply congrArg (fun k =>
            Isotope.TAC.Densem.Monadic.Operand.denote M s.env
              (Isotope.TAC.Densem.Classical.operand rhs) >>= k)
          funext a
          exact ih (Store.set M s x a)
      | assignPair x y rhs =>
          simp only [block, Isotope.TAC.Densem.Classical.instructions,
            Isotope.TAC.Densem.Monadic.Block.denote, bind_assoc]
          apply congrArg (fun k =>
            Isotope.TAC.Densem.Monadic.Operand.denote M s.env
              (Isotope.TAC.Densem.Classical.operand rhs) >>= k)
          funext a
          apply congrArg (fun k => M.split a >>= k)
          funext p
          rcases p with ⟨ax, ay⟩
          exact ih (Store.set M (Store.set M s x ax) y ay)

structure State [DecidableEq ν] [DecidableEq κ]
    (g : Isotope.TAC.Classical.CFG ν φ κ) where
  store : Store M (sourceVars g)
  pred : BlockId κ
  label : κ
  edge : sourceVars g = [] ∨ pred ∈ predecessors g (.named label)

def State.forget [DecidableEq ν] [DecidableEq κ]
    {g : Isotope.TAC.Classical.CFG ν φ κ} (s : State M g) :
    GuardedState M ν κ := (s.store.env, s.pred, s.label)

def Store.restrict [DecidableEq ν] {vars : List ν} (s : Store M vars) :
    Store M vars where
  env := Isotope.TAC.Densem.Convert.Monadic.restrict M vars s.env
  total := by
    intro x hx
    rcases s.total x hx with ⟨a, ha⟩
    exact ⟨a, by simp [Isotope.TAC.Densem.Convert.Monadic.restrict, hx, ha]⟩

def step [Monad m] [DecidableEq ν] [DecidableEq κ]
    (g : Isotope.TAC.Classical.CFG ν φ κ) :
    State M g → m (M.Val ⊕ State M g)
  | s => match hs : Isotope.TAC.Densem.Phi.lookup g s.label with
      | none => M.fail
      | some b => do
          let result ← block M s.store b.body b.terminator
          match he : result.2.1 with
          | .return a => pure (.inl a)
          | .branch next =>
              pure (.inr {
                store := result.1.restrict
                pred := .named s.label
                label := next
                edge := by
                  by_cases hempty : sourceVars g = []
                  · exact .inl hempty
                  · apply Or.inr
                    have hcfg : g.lookup (.named s.label) = some b := by
                      rw [← Isotope.TAC.Densem.Lookup.phi_lookup_eq]
                      exact hs
                    have htarget : next ∈ b.terminator.targets := by
                      have hv := result.2.2
                      rw [he] at hv
                      exact hv
                    apply (mem_predecessors g (.named s.label) (.named next)).2
                    constructor
                    · unfold Isotope.TAC.Classical.CFG.successors
                      rw [hcfg]
                      simpa using htarget
                    · apply Or.inr
                      refine ⟨s.label, ?_, rfl⟩
                      unfold Isotope.TAC.Classical.CFG.labels
                      exact List.mem_map.mpr ⟨(s.label, b),
                        Isotope.TAC.Densem.Convert.lookup_some_mem hs, rfl⟩ })

theorem step_forget_source [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    [Isotope.TAC.Densem.Phi.Monadic.LawfulFailure M]
    (g : Isotope.TAC.Classical.CFG ν φ κ) (s : State M g) :
    (step M g s >>= fun result => pure (Sum.map id (State.forget M) result)) =
      sourcePredStep M g (State.forget M s) := by
  simp only [step, sourcePredStep, State.forget, sourceStepOn]
  split
  next hs =>
      simp only [hs]
      exact (Isotope.TAC.Densem.Phi.Monadic.LawfulFailure.fail_bind _).trans
        (Isotope.TAC.Densem.Phi.Monadic.LawfulFailure.fail_bind _).symm
  next b hs =>
      simp only [hs, bind_assoc]
      have hb := block_forget M s.store b.body b.terminator
      rw [show Isotope.TAC.Densem.Classical.block b =
        Isotope.TAC.Densem.Classical.instructions b.body
          (Isotope.TAC.Densem.Classical.terminator b.terminator) from rfl]
      rw [← hb]
      simp only [bind_assoc]
      apply congrArg (fun k => block M s.store b.body b.terminator >>= k)
      funext result
      rcases result with ⟨store, exit⟩
      rcases exit with ⟨exit, hexit⟩
      cases exit <;> simp [Store.restrict, State.forget]

private theorem sourcePredStep_some [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (g : Isotope.TAC.Classical.CFG ν φ κ)
    (store : MEnv M ν) (pred : BlockId κ) (label : κ)
    (b : Isotope.TAC.Classical.Block ν φ κ)
    (hs : Isotope.TAC.Densem.Phi.lookup g label = some b) :
    sourcePredStep M g (store, pred, label) = (do
      let result ← Isotope.TAC.Densem.Monadic.Block.denote M store
        (Isotope.TAC.Densem.Classical.block b)
      match result.2 with
      | .return a => pure (.inl a)
      | .branch next => pure (.inr
          (restrict M (sourceVars g) result.1, .named label, next))) := by
  simp only [sourcePredStep, sourceStepOn, hs, bind_assoc]
  apply congrArg (fun k => Isotope.TAC.Densem.Monadic.Block.denote M store
    (Isotope.TAC.Densem.Classical.block b) >>= k)
  funext result
  rcases result with ⟨rho, exit⟩
  cases exit <;> simp

theorem step_forget_guarded [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    [Isotope.TAC.Densem.Phi.Monadic.LawfulFailure M]
    (g : Isotope.TAC.Classical.CFG ν φ κ) (s : State M g) :
    (step M g s >>= fun result => pure (Sum.map id (State.forget M) result)) =
      guardedSourceStep M g (State.forget M s) := by
  rw [step_forget_source M g s]
  rcases s with ⟨store, pred, label, hedge⟩
  simp only [State.forget, guardedSourceStep]
  split
  next hs =>
      simp only [sourcePredStep, sourceStepOn, hs]
      exact (Isotope.TAC.Densem.Phi.Monadic.LawfulFailure.fail_bind
        (M := M) (fun result : M.Val ⊕ (MEnv M ν × κ) =>
          pure (Sum.map id (fun next =>
            (next.1, BlockId.named label, next.2)) result)))
  next b hs =>
      have hpresent : allPresent M (sourceVars g) store.env = true :=
        (allPresent_eq_true_iff M _ _).2 store.total
      rw [sourcePredStep_some M g store.env pred label b hs]
      rw [dif_pos hpresent]
      rcases hedge with hempty | hp
      · simp only [hempty, bind_assoc, pure_bind]
        rfl
      · by_cases hempty : sourceVars g = []
        · simp only [hempty, bind_assoc, pure_bind]
          rfl
        · obtain ⟨x, xs, hvars⟩ := List.exists_cons_of_ne_nil hempty
          simp only [hvars, hp, if_true, bind_assoc, pure_bind]
          rfl

theorem iter_forget_source [Monad m] [LawfulMonad m]
    [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
    [DecidableEq ν] [DecidableEq κ]
    [Isotope.TAC.Densem.Phi.Monadic.LawfulFailure M]
    (g : Isotope.TAC.Classical.CFG ν φ κ) (s : State M g) :
    Isotope.Elgot.iter (step M g) s =
      Isotope.Elgot.iter (sourcePredStep M g) (State.forget M s) := by
  let f := step M g
  let target := sourcePredStep M g
  have comm : Isotope.Elgot.kcomp f
      (Isotope.Elgot.liftPure (Sum.map id (State.forget M))) =
      Isotope.Elgot.kcomp (Isotope.Elgot.liftPure (State.forget M)) target := by
    funext state
    simp only [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
      Function.comp_apply, pure_bind]
    exact step_forget_source M g state
  have hu := Isotope.Elgot.LawfulElgotMonad.uniformity f target
    (State.forget M) comm
  change Isotope.Elgot.iter f s =
    Isotope.Elgot.iter target (State.forget M s)
  rw [hu]
  simp [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure]

theorem iter_forget_guarded [Monad m] [LawfulMonad m]
    [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
    [DecidableEq ν] [DecidableEq κ]
    [Isotope.TAC.Densem.Phi.Monadic.LawfulFailure M]
    (g : Isotope.TAC.Classical.CFG ν φ κ) (s : State M g) :
    Isotope.Elgot.iter (step M g) s =
      Isotope.Elgot.iter (guardedSourceStep M g) (State.forget M s) := by
  let f := step M g
  let target := guardedSourceStep M g
  have comm : Isotope.Elgot.kcomp f
      (Isotope.Elgot.liftPure (Sum.map id (State.forget M))) =
      Isotope.Elgot.kcomp (Isotope.Elgot.liftPure (State.forget M)) target := by
    funext state
    simp only [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
      Function.comp_apply, pure_bind]
    exact step_forget_guarded M g state
  have hu := Isotope.Elgot.LawfulElgotMonad.uniformity f target
    (State.forget M) comm
  change Isotope.Elgot.iter f s =
    Isotope.Elgot.iter target (State.forget M s)
  rw [hu]
  simp [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure]

/-- On proof-carrying reachable states, the executable guards are
observationally irrelevant to complete-Elgot iteration. -/
theorem iter_guarded_eq_source [Monad m] [LawfulMonad m]
    [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
    [DecidableEq ν] [DecidableEq κ]
    [Isotope.TAC.Densem.Phi.Monadic.LawfulFailure M]
    (g : Isotope.TAC.Classical.CFG ν φ κ) (s : State M g) :
    Isotope.Elgot.iter (guardedSourceStep M g) (State.forget M s) =
      Isotope.Elgot.iter (sourcePredStep M g) (State.forget M s) := by
  rw [← iter_forget_guarded M g s, iter_forget_source M g s]

end Isotope.TAC.Densem.Convert.Monadic.Valid
