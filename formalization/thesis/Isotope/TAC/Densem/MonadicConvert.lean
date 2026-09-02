import Isotope.TAC.Densem.Convert

/-! # Local monadic correctness of canonical TAC-to-SSA renaming

These lemmas are the effectful counterpart of the executable simulations in
`Densem.Convert`.  They deliberately stop at control-flow iteration: the
whole-CFG theorem additionally has to package the invariant that every
reachable converted store represents a total source store.
-/

namespace Isotope.TAC.Densem.Convert.Monadic

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert

universe u v

variable {ν : Type u} {κ : Type} {φ : Type v} {m : Type → Type}
variable (M : Isotope.TAC.Densem.Monadic.Model φ m)

abbrev MEnv := Isotope.TAC.Densem.Monadic.Env M

/-- A converted store represents a source store through the reaching-version
environment at the current program point. -/
def EnvRel (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ)) : Prop :=
  ∀ x, target (current x) = source x

/-- Agreement on the finite interface that can still be observed.  This is
the invariant used at CFG boundaries, where unrelated source variables need
not be represented. -/
def EnvRelOn (needed : List ν)
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ)) : Prop :=
  ∀ x ∈ needed, target (current x) = source x

/-- Read a versioned store through a reaching-version environment.  This is
the observation map used below to state equality of effectful computations
whose raw output stores have different variable types. -/
def project (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (target : MEnv M (Version ν κ)) : MEnv M ν :=
  fun x => target (current x)

theorem EnvRel.project_eq
    {current : Isotope.TAC.Classical.Convert.Env ν κ}
    {source : MEnv M ν} {target : MEnv M (Version ν κ)}
    (hrel : EnvRel (M := M) current source target) :
    project (M := M) current target = source := by
  funext x
  exact hrel x

theorem EnvRel.update [DecidableEq ν] [DecidableEq κ]
    {current : Isotope.TAC.Classical.Convert.Env ν κ}
    {source : MEnv M ν} {target : MEnv M (Version ν κ)}
    (hrel : EnvRel (M := M) current source target)
    (x : ν) (dst : Version ν κ) (a : M.Val)
    (hfresh : ∀ y, y ≠ x → current y ≠ dst) :
    EnvRel (M := M) (update current x dst)
      (Isotope.TAC.Densem.Monadic.Env.set source x a)
      (Isotope.TAC.Densem.Monadic.Env.set target dst a) := by
  intro y
  by_cases e : y = x
  · subst y
    simp [Isotope.TAC.Classical.Convert.update,
      Isotope.TAC.Densem.Monadic.Env.set]
  · simp only [Isotope.TAC.Classical.Convert.update,
      Isotope.TAC.Densem.Monadic.Env.set, e, if_false, hfresh y e]
    exact hrel y

theorem EnvRelOn.update [DecidableEq ν] [DecidableEq κ]
    {needed : List ν}
    {current : Isotope.TAC.Classical.Convert.Env ν κ}
    {source : MEnv M ν} {target : MEnv M (Version ν κ)}
    (hrel : EnvRelOn (M := M) needed current source target)
    (x : ν) (dst : Version ν κ) (a : M.Val)
    (hfresh : ∀ y, y ≠ x → current y ≠ dst) :
    EnvRelOn (M := M) needed (update current x dst)
      (Isotope.TAC.Densem.Monadic.Env.set source x a)
      (Isotope.TAC.Densem.Monadic.Env.set target dst a) := by
  intro y hy
  by_cases e : y = x
  · subst y
    simp [Isotope.TAC.Classical.Convert.update,
      Isotope.TAC.Densem.Monadic.Env.set]
  · simp only [Isotope.TAC.Classical.Convert.update,
      Isotope.TAC.Densem.Monadic.Env.set, e, if_false, hfresh y e]
    exact hrel y hy

/-- Forget store entries outside a finite compiler interface. -/
def restrict [DecidableEq ν] (needed : List ν) (source : MEnv M ν) : MEnv M ν :=
  fun x => if x ∈ needed then source x else none

theorem EnvRelOn.restrict_project_eq [DecidableEq ν]
    {needed : List ν}
    {current : Isotope.TAC.Classical.Convert.Env ν κ}
    {source : MEnv M ν} {target : MEnv M (Version ν κ)}
    (hrel : EnvRelOn (M := M) needed current source target) :
    restrict (M := M) needed (project (M := M) current target) =
      restrict (M := M) needed source := by
  funext x
  by_cases hx : x ∈ needed
  · simp [restrict, hx, project, hrel x hx]
  · simp [restrict, hx]

theorem value_denote [Monad m] [LawfulMonad m]
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRel (M := M) current source target)
    (a : Isotope.TAC.Classical.Value ν) :
    Isotope.TAC.Densem.Monadic.Value.denote M target
        (Isotope.TAC.Densem.Classical.value (renameValue current a)) =
      Isotope.TAC.Densem.Monadic.Value.denote M source
        (Isotope.TAC.Densem.Classical.value a) := by
  induction a with
  | var x =>
      simp only [renameValue, Isotope.TAC.Densem.Classical.value,
        Isotope.TAC.Densem.Monadic.Value.denote]
      rw [hrel x]
  | unit => rfl
  | pair left right ihl ihr =>
      simp only [renameValue, Isotope.TAC.Densem.Classical.value,
        Isotope.TAC.Densem.Monadic.Value.denote]
      rw [ihl, ihr]

theorem operand_denote [Monad m] [LawfulMonad m]
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRel (M := M) current source target)
    (a : Isotope.TAC.Classical.Operand ν φ) :
    Isotope.TAC.Densem.Monadic.Operand.denote M target
        (Isotope.TAC.Densem.Classical.operand (renameOperand current a)) =
      Isotope.TAC.Densem.Monadic.Operand.denote M source
        (Isotope.TAC.Densem.Classical.operand a) := by
  cases a <;>
    simp only [renameOperand, Isotope.TAC.Densem.Classical.operand,
      Isotope.TAC.Densem.Monadic.Operand.denote] <;>
    rw [value_denote M current source target hrel]

theorem value_denote_on [Monad m] [LawfulMonad m]
    (needed : List ν) (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRelOn (M := M) needed current source target)
    (a : Isotope.TAC.Classical.Value ν)
    (huses : ∀ x ∈ a.uses, x ∈ needed) :
    Isotope.TAC.Densem.Monadic.Value.denote M target
        (Isotope.TAC.Densem.Classical.value (renameValue current a)) =
      Isotope.TAC.Densem.Monadic.Value.denote M source
        (Isotope.TAC.Densem.Classical.value a) := by
  induction a with
  | var x =>
      simp only [Isotope.TAC.Classical.Value.uses, List.mem_singleton] at huses
      simp only [renameValue, Isotope.TAC.Densem.Classical.value,
        Isotope.TAC.Densem.Monadic.Value.denote]
      rw [hrel x (huses x rfl)]
  | unit => rfl
  | pair left right ihl ihr =>
      simp only [Isotope.TAC.Classical.Value.uses, List.mem_append] at huses
      simp only [renameValue, Isotope.TAC.Densem.Classical.value,
        Isotope.TAC.Densem.Monadic.Value.denote]
      rw [ihl (fun x hx => huses x (.inl hx)),
        ihr (fun x hx => huses x (.inr hx))]

theorem operand_denote_on [Monad m] [LawfulMonad m]
    (needed : List ν) (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRelOn (M := M) needed current source target)
    (a : Isotope.TAC.Classical.Operand ν φ)
    (huses : ∀ x ∈ a.uses, x ∈ needed) :
    Isotope.TAC.Densem.Monadic.Operand.denote M target
        (Isotope.TAC.Densem.Classical.operand (renameOperand current a)) =
      Isotope.TAC.Densem.Monadic.Operand.denote M source
        (Isotope.TAC.Densem.Classical.operand a) := by
  cases a with
  | value v | app _ v | inl v | inr v =>
      simp only [renameOperand, Isotope.TAC.Densem.Classical.operand,
        Isotope.TAC.Densem.Monadic.Operand.denote]
      rw [value_denote_on M needed current source target hrel v
        (fun x hx => huses x (by
          simpa [Isotope.TAC.Classical.Operand.uses] using hx))]
  | abort => rfl

theorem terminator_denote [Monad m] [LawfulMonad m]
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRel (M := M) current source target)
    (t : Isotope.TAC.Classical.Terminator ν φ κ) :
    Isotope.TAC.Densem.Monadic.Terminator.denote M target
        (Isotope.TAC.Densem.Classical.terminator (renameTerminator current t)) =
      Isotope.TAC.Densem.Monadic.Terminator.denote M source
        (Isotope.TAC.Densem.Classical.terminator (κ := κ) t) := by
  induction t with
  | br => rfl
  | ret a =>
      simp only [renameTerminator, Isotope.TAC.Densem.Classical.terminator,
        Isotope.TAC.Densem.Monadic.Terminator.denote]
      rw [value_denote M current source target hrel]
  | cond c left right ihl ihr =>
      simp only [renameTerminator, Isotope.TAC.Densem.Classical.terminator,
        Isotope.TAC.Densem.Monadic.Terminator.denote]
      rw [operand_denote M current source target hrel]
      apply bind_congr
      intro b
      cases b
      · exact ihr
      · exact ihl

theorem terminator_denote_on [Monad m] [LawfulMonad m]
    (needed : List ν) (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRelOn (M := M) needed current source target)
    (t : Isotope.TAC.Classical.Terminator ν φ κ)
    (huses : ∀ x ∈ t.uses, x ∈ needed) :
    Isotope.TAC.Densem.Monadic.Terminator.denote M target
        (Isotope.TAC.Densem.Classical.terminator (renameTerminator current t)) =
      Isotope.TAC.Densem.Monadic.Terminator.denote M source
        (Isotope.TAC.Densem.Classical.terminator (κ := κ) t) := by
  induction t with
  | br => rfl
  | ret value =>
      simp only [renameTerminator, Isotope.TAC.Densem.Classical.terminator,
        Isotope.TAC.Densem.Monadic.Terminator.denote]
      rw [value_denote_on M needed current source target hrel value
        (fun x hx => huses x (by
          simpa [Isotope.TAC.Classical.Terminator.uses] using hx))]
  | cond c left right ihl ihr =>
      simp only [renameTerminator, Isotope.TAC.Densem.Classical.terminator,
        Isotope.TAC.Densem.Monadic.Terminator.denote]
      rw [operand_denote_on M needed current source target hrel c
        (fun x hx => huses x (by
          simp only [Isotope.TAC.Classical.Terminator.uses, List.mem_append]
          exact .inl (.inl hx)))]
      apply bind_congr
      intro b
      cases b
      · exact ihr (fun x hx => huses x (by
          simp only [Isotope.TAC.Classical.Terminator.uses, List.mem_append]
          exact .inr hx))
      · exact ihl (fun x hx => huses x (by
          simp only [Isotope.TAC.Classical.Terminator.uses, List.mem_append]
          exact .inl (.inr hx)))

/-- Effectful straight-line conversion correctness.  Observing the target
store through the compiler's final reaching-version environment gives exactly
the source computation, including its primitive effects and failures.

Unlike a merely successful-run simulation, this equality does not inspect the
monad and therefore also covers divergence and failure.  No law for `M.fail`
is needed locally: conversion neither introduces nor removes an abort. -/
theorem body_denote_project {ν : Type} [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (bid : BlockId κ) (i : Nat)
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (xs : List (Isotope.TAC.Classical.Instr ν φ))
    (t : Isotope.TAC.Classical.Terminator ν φ κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRel (M := M) current source target)
    (hfresh : Isotope.TAC.Densem.Convert.FreshFor bid i current xs) :
    (Isotope.TAC.Densem.Monadic.Block.denote M target
        (Isotope.TAC.Densem.Classical.instructions
          (body bid i current xs).1
          (Isotope.TAC.Densem.Classical.terminator
            (renameTerminator (body bid i current xs).2 t))) >>= fun result =>
      pure (project (M := M) (body bid i current xs).2 result.1, result.2)) =
    Isotope.TAC.Densem.Monadic.Block.denote M source
      (Isotope.TAC.Densem.Classical.instructions xs
        (Isotope.TAC.Densem.Classical.terminator t)) := by
  induction xs generalizing i current source target with
  | nil =>
      simp only [body, Isotope.TAC.Densem.Classical.instructions,
        Isotope.TAC.Densem.Monadic.Block.denote]
      rw [terminator_denote M current source target hrel]
      rw [map_eq_pure_bind, map_eq_pure_bind, bind_assoc]
      apply congrArg (fun q =>
        Isotope.TAC.Densem.Monadic.Terminator.denote M source
          (Isotope.TAC.Densem.Classical.terminator t) >>= q)
      funext exit
      simp only [pure_bind]
      rw [hrel.project_eq]
  | cons instr rest ih =>
      cases instr with
      | assign x rhs =>
          rcases hfresh with ⟨hdst, hrest⟩
          simp only [body, Isotope.TAC.Densem.Classical.instructions,
            Isotope.TAC.Densem.Monadic.Block.denote]
          rw [operand_denote M current source target hrel]
          simp only [bind_assoc]
          apply congrArg (fun q =>
            Isotope.TAC.Densem.Monadic.Operand.denote M source
              (Isotope.TAC.Densem.Classical.operand rhs) >>= q)
          funext a
          exact ih (i + 1) (update current x (Version.instr bid i 0 x))
            (Isotope.TAC.Densem.Monadic.Env.set source x a)
            (Isotope.TAC.Densem.Monadic.Env.set target
              (Version.instr bid i 0 x) a)
            (EnvRel.update M hrel x (Version.instr bid i 0 x) a hdst)
            hrest
      | assignPair x y rhs =>
          rcases hfresh with ⟨hdx, hdy, hrest⟩
          simp only [body, Isotope.TAC.Densem.Classical.instructions,
            Isotope.TAC.Densem.Monadic.Block.denote]
          rw [operand_denote M current source target hrel]
          simp only [bind_assoc]
          apply congrArg (fun q =>
            Isotope.TAC.Densem.Monadic.Operand.denote M source
              (Isotope.TAC.Densem.Classical.operand rhs) >>= q)
          funext a
          apply congrArg (fun q => M.split a >>= q)
          funext p
          rcases p with ⟨ax, ay⟩
          have hx := EnvRel.update M hrel x (Version.instr bid i 0 x) ax hdx
          have hxy := EnvRel.update M hx y (Version.instr bid i 1 y) ay hdy
          exact ih (i + 1)
            (update (update current x (Version.instr bid i 0 x)) y
              (Version.instr bid i 1 y))
            ((Isotope.TAC.Densem.Monadic.Env.set source x ax).set y ay)
            ((Isotope.TAC.Densem.Monadic.Env.set target
              (Version.instr bid i 0 x) ax).set
                (Version.instr bid i 1 y) ay)
            hxy hrest

/-- Finite-interface variant of `body_denote_project`.  This removes the
spurious requirement that the compiler's finite source-variable list exhaust
the ambient variable type.  Both result stores are observed only on variables
the program can use. -/
theorem body_denote_restrict_project {ν : Type} [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (needed : List ν) (bid : BlockId κ) (i : Nat)
    (current : Isotope.TAC.Classical.Convert.Env ν κ)
    (xs : List (Isotope.TAC.Classical.Instr ν φ))
    (t : Isotope.TAC.Classical.Terminator ν φ κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRelOn (M := M) needed current source target)
    (hfresh : Isotope.TAC.Densem.Convert.FreshFor bid i current xs)
    (hins : ∀ ins ∈ xs, ∀ x ∈ ins.uses, x ∈ needed)
    (hterm : ∀ x ∈ t.uses, x ∈ needed) :
    (Isotope.TAC.Densem.Monadic.Block.denote M target
        (Isotope.TAC.Densem.Classical.instructions
          (body bid i current xs).1
          (Isotope.TAC.Densem.Classical.terminator
            (renameTerminator (body bid i current xs).2 t))) >>= fun result =>
      pure (restrict (M := M) needed
        (project (M := M) (body bid i current xs).2 result.1), result.2)) =
    (Isotope.TAC.Densem.Monadic.Block.denote M source
        (Isotope.TAC.Densem.Classical.instructions xs
          (Isotope.TAC.Densem.Classical.terminator t)) >>= fun result =>
      pure (restrict (M := M) needed result.1, result.2)) := by
  induction xs generalizing i current source target with
  | nil =>
      simp only [body, Isotope.TAC.Densem.Classical.instructions,
        Isotope.TAC.Densem.Monadic.Block.denote]
      rw [terminator_denote_on M needed current source target hrel t hterm]
      simp only [map_eq_pure_bind, bind_assoc]
      apply congrArg (fun q =>
        Isotope.TAC.Densem.Monadic.Terminator.denote M source
          (Isotope.TAC.Densem.Classical.terminator t) >>= q)
      funext exit
      simp only [pure_bind]
      rw [hrel.restrict_project_eq]
  | cons instr rest ih =>
      have htail : ∀ ins ∈ rest, ∀ x ∈ ins.uses, x ∈ needed := by
        intro ins hi x hx
        exact hins ins (List.mem_cons_of_mem instr hi) x hx
      cases instr with
      | assign x rhs =>
          rcases hfresh with ⟨hdst, hrest⟩
          simp only [body, Isotope.TAC.Densem.Classical.instructions,
            Isotope.TAC.Densem.Monadic.Block.denote]
          rw [operand_denote_on M needed current source target hrel rhs
            (fun y hy => hins (.assign x rhs) (by simp) y hy)]
          simp only [bind_assoc]
          apply congrArg (fun q =>
            Isotope.TAC.Densem.Monadic.Operand.denote M source
              (Isotope.TAC.Densem.Classical.operand rhs) >>= q)
          funext a
          exact ih (i + 1) (update current x (Version.instr bid i 0 x))
            (Isotope.TAC.Densem.Monadic.Env.set source x a)
            (Isotope.TAC.Densem.Monadic.Env.set target
              (Version.instr bid i 0 x) a)
            (EnvRelOn.update M hrel x (Version.instr bid i 0 x) a hdst)
            hrest htail
      | assignPair x y rhs =>
          rcases hfresh with ⟨hdx, hdy, hrest⟩
          simp only [body, Isotope.TAC.Densem.Classical.instructions,
            Isotope.TAC.Densem.Monadic.Block.denote]
          rw [operand_denote_on M needed current source target hrel rhs
            (fun z hz => hins (.assignPair x y rhs) (by simp) z hz)]
          simp only [bind_assoc]
          apply congrArg (fun q =>
            Isotope.TAC.Densem.Monadic.Operand.denote M source
              (Isotope.TAC.Densem.Classical.operand rhs) >>= q)
          funext a
          apply congrArg (fun q => M.split a >>= q)
          funext p
          rcases p with ⟨ax, ay⟩
          have hx := EnvRelOn.update M hrel x
            (Version.instr bid i 0 x) ax hdx
          have hxy := EnvRelOn.update M hx y
            (Version.instr bid i 1 y) ay hdy
          exact ih (i + 1)
            (update (update current x (Version.instr bid i 0 x)) y
              (Version.instr bid i 1 y))
            ((Isotope.TAC.Densem.Monadic.Env.set source x ax).set y ay)
            ((Isotope.TAC.Densem.Monadic.Env.set target
              (Version.instr bid i 0 x) ax).set
                (Version.instr bid i 1 y) ay)
            hxy hrest htail

/-- Block-level form of `body_denote_project`, ready to be used after the
simultaneous phi installation at a CFG edge.  The classical bridge erases the
phi list here; its semantics is handled separately by `Phi.enter`. -/
theorem convertBlock_denote_project {ν : Type} [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (cfg : Isotope.TAC.Classical.CFG ν φ κ) (vars : List ν)
    (bid : BlockId κ) (b : Isotope.TAC.Classical.Block ν φ κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hrel : EnvRel (M := M) (startEnv bid) source target)
    (hfresh : Isotope.TAC.Densem.Convert.FreshFor bid 0 (startEnv bid) b.body) :
    (Isotope.TAC.Densem.Monadic.Block.denote M target
        (Isotope.TAC.Densem.Classical.block (convertBlock cfg vars bid b)) >>=
      fun result => pure
        (project (M := M) (endEnv bid b) result.1, result.2)) =
    Isotope.TAC.Densem.Monadic.Block.denote M source
      (Isotope.TAC.Densem.Classical.block b) := by
  simpa [Isotope.TAC.Densem.Classical.block, convertBlock, endEnv] using
    body_denote_project M bid 0 (startEnv bid) b.body b.terminator
      source target hrel hfresh

end Isotope.TAC.Densem.Convert.Monadic
