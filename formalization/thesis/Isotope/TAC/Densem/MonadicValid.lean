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

end Isotope.TAC.Densem.Convert.Monadic.Valid
