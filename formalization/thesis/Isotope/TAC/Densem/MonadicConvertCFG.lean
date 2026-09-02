import Isotope.TAC.Densem.MonadicConvert
import Isotope.TAC.Densem.Fresh

/-! # CFG boundary invariants for monadic TAC-to-SSA conversion -/

namespace Isotope.TAC.Densem.Convert.Monadic

open Isotope.TAC.Classical
open Isotope.TAC.Classical.Convert

universe v

variable {ν : Type} {κ : Type} {φ : Type v} {m : Type → Type}
variable (M : Isotope.TAC.Densem.Monadic.Model φ m)

/-- Total source stores are the invariant carried by the CFG simulation. -/
def Total (source : MEnv M ν) : Prop := ∀ x, ∃ a, source x = some a

/-- The monadic analogue of the canonical external target store. -/
def externalEnv (source : MEnv M ν) : MEnv M (Version ν κ)
  | .external x => source x
  | .phi _ _ | .instr _ _ _ _ => none

@[simp] theorem externalEnv_external (source : MEnv M ν) (x : ν) :
    externalEnv (M := M) (κ := κ) source (.external x) = source x := rfl

theorem external_envRel (source : MEnv M ν) :
    EnvRel (M := M) (startEnv (.entry : BlockId κ)) source
      (externalEnv (M := M) (κ := κ) source) := by
  intro x
  rfl

/-- At a CFG edge, a target store represents the total source store using
the versions reaching the end of the predecessor block. -/
def BoundaryRel [DecidableEq ν] (sourceCfg : Isotope.TAC.Classical.CFG ν φ κ)
    (pred : BlockId κ) (predBlock : Isotope.TAC.Classical.Block ν φ κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ)) : Prop :=
  Total (M := M) source ∧
    EnvRelOn (M := M) (sourceVars sourceCfg) (endEnv pred predBlock) source target

private theorem select_filterMap [DecidableEq κ]
    (ps : List (BlockId κ)) (pred : BlockId κ)
    (f : BlockId κ → Option α)
    (g : BlockId κ → α → Isotope.TAC.Classical.Value β)
    (hmem : pred ∈ ps) (hf : f pred = some a) :
    Isotope.TAC.Densem.Phi.incoming pred
      (ps.filterMap fun q => (f q).map fun v =>
        ({ predecessor := q, value := g q v } : Isotope.TAC.Classical.Incoming β κ)) =
      some (g pred a) := by
  induction ps with
  | nil => simp at hmem
  | cons q qs ih =>
      rw [List.filterMap_cons]
      by_cases e : pred = q
      · subst q
        rw [hf]
        simp [Isotope.TAC.Densem.Phi.incoming]
      · have hm : pred ∈ qs := (List.mem_cons.mp hmem).resolve_left e
        cases hq : f q with
        | none =>
            simp only [hq, Option.map_none]
            exact ih hm
        | some v =>
            simp only [hq, Option.map_some]
            unfold Isotope.TAC.Densem.Phi.incoming
            rw [List.find?_cons]
            have ene : q ≠ pred := fun h => e h.symm
            simp only [ene, decide_false, if_false, Option.map_eq_map]
            exact ih hm

theorem incoming_select [DecidableEq ν] [DecidableEq κ]
    (source : Isotope.TAC.Classical.CFG ν φ κ) (bid pred : BlockId κ) (x : ν)
    (b : Isotope.TAC.Classical.Block ν φ κ) (hpred : pred ∈ predecessors source bid)
    (hb : source.lookup pred = some b) :
    Isotope.TAC.Densem.Phi.incoming pred (incoming source bid x) =
      some (.var (endEnv pred b x)) := by
  unfold incoming blockAt
  exact select_filterMap (predecessors source bid) pred (source.lookup ·)
    (fun q block => Isotope.TAC.Classical.Value.var (endEnv q block x)) hpred hb

/-- Simultaneous monadic phi evaluation reads precisely the reaching source
values.  The right-hand sides are all evaluated in the pre-installation store. -/
theorem assignments_convert [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (source : Isotope.TAC.Classical.CFG ν φ κ) (vars : List ν) (label : κ)
    (pred : BlockId κ) (b : Isotope.TAC.Classical.Block ν φ κ)
    (target : MEnv M (Version ν κ)) (values : ν → M.Val)
    (hpred : pred ∈ predecessors source (.named label))
    (hb : source.lookup pred = some b)
    (hvalues : ∀ x ∈ vars, target (endEnv pred b x) = some (values x)) :
    Isotope.TAC.Densem.Phi.Monadic.assignments M target pred
        (phis source vars label) =
      (pure (vars.map fun x => (Version.phi label x, values x)) :
        m (List (Version ν κ × M.Val))) := by
  induction vars with
  | nil => rfl
  | cons x xs ih =>
      simp only [phis, List.map_cons,
        Isotope.TAC.Densem.Phi.Monadic.assignments]
      rw [incoming_select source (.named label) pred x b hpred hb]
      simp only [Isotope.TAC.Densem.Classical.value,
        Isotope.TAC.Densem.Monadic.Value.denote]
      rw [hvalues x (by simp)]
      simp only [pure_bind]
      change (do
        let tail ← Isotope.TAC.Densem.Phi.Monadic.assignments M target pred
          (phis source xs label)
        pure ((Version.phi label x, values x) :: tail)) = _
      rw [ih (fun y hy => hvalues y (by simp [hy]))]
      simp

theorem install_phi_get [DecidableEq ν] [DecidableEq κ]
    (vars : List ν) (hvars : vars.Nodup) (label : κ)
    (values : ν → M.Val) (target : MEnv M (Version ν κ))
    (x : ν) (hx : x ∈ vars) :
    Isotope.TAC.Densem.Phi.Monadic.install target
        (vars.map fun y => (Version.phi label y, values y))
        (Version.phi label x) = some (values x) := by
  induction vars generalizing target with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.nodup_cons] at hvars
      simp only [List.map_cons, Isotope.TAC.Densem.Phi.Monadic.install]
      rcases List.mem_cons.mp hx with rfl | hx
      · have absent : ∀ (zs : List ν) (hz : x ∉ zs)
            (ρ : MEnv M (Version ν κ)),
            Isotope.TAC.Densem.Phi.Monadic.install ρ
                (zs.map fun z => (Version.phi label z, values z))
                (Version.phi label x) = ρ (Version.phi label x) := by
          intro zs hz ρ
          induction zs generalizing ρ with
          | nil => rfl
          | cons z zs iz =>
              simp only [List.mem_cons, not_or] at hz
              simp only [List.map_cons, Isotope.TAC.Densem.Phi.Monadic.install]
              rw [iz hz.2]
              simp [Isotope.TAC.Densem.Monadic.Env.set, hz.1]
        rw [absent ys hvars.1]
        simp [Isotope.TAC.Densem.Monadic.Env.set]
      · exact ih hvars.2 (target :=
          Isotope.TAC.Densem.Monadic.Env.set target
            (Version.phi label y) (values y)) hx

theorem installed_phi_envRelOn [DecidableEq ν] [DecidableEq κ]
    (vars : List ν) (hvars : vars.Nodup) (label : κ)
    (values : ν → M.Val) (target : MEnv M (Version ν κ)) :
    EnvRelOn (M := M) vars (startEnv (.named label))
      (fun x => some (values x))
      (Isotope.TAC.Densem.Phi.Monadic.install target
        (vars.map fun x => (Version.phi label x, values x))) := by
  intro x hx
  exact install_phi_get M vars hvars label values target x hx

/-- Entering a converted named block first establishes the canonical
`startEnv` relation.  This is the CFG-edge commuting square needed before
applying straight-line conversion correctness. -/
theorem enter_named_prepare [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (sourceCfg : Isotope.TAC.Classical.CFG ν φ κ) (label : κ) (pred : BlockId κ)
    (predBlock block : Isotope.TAC.Classical.Block ν φ κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hpred : pred ∈ predecessors sourceCfg (.named label))
    (hpredBlock : sourceCfg.lookup pred = some predBlock)
    (htotal : Total (M := M) source)
    (hrel : EnvRelOn (M := M) (sourceVars sourceCfg)
      (endEnv pred predBlock) source target) :
    Isotope.TAC.Densem.Phi.Monadic.enter M target pred
        (convertBlock sourceCfg (sourceVars sourceCfg) (.named label) block) =
      Isotope.TAC.Densem.Monadic.Block.denote M
        (Isotope.TAC.Densem.Phi.Monadic.install target
          ((sourceVars sourceCfg).map fun x =>
            (Version.phi label x, Classical.choose (htotal x))))
        (Isotope.TAC.Densem.Classical.block
          (convertBlock sourceCfg (sourceVars sourceCfg) (.named label) block)) := by
  let values : ν → M.Val := fun x => Classical.choose (htotal x)
  have hvalue : ∀ x, source x = some (values x) := fun x =>
    Classical.choose_spec (htotal x)
  have ha := assignments_convert M sourceCfg (sourceVars sourceCfg) label pred
    predBlock target values hpred hpredBlock
      (fun x hx => by rw [hrel x hx, hvalue x])
  unfold Isotope.TAC.Densem.Phi.Monadic.enter
  simp only [convertBlock]
  rw [ha]
  simp [values]

/-- Full named-block commuting theorem when the finite compiler interface
covers the source variable type.  This form exposes exactly the invariant
needed to make the theorem a branch of an Elgot-uniformity argument. -/
theorem enter_named_denote [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (sourceCfg : Isotope.TAC.Classical.CFG ν φ κ)
    (label : κ) (pred : BlockId κ)
    (predBlock block : Isotope.TAC.Classical.Block ν φ κ)
    (source : MEnv M ν) (target : MEnv M (Version ν κ))
    (hpred : pred ∈ predecessors sourceCfg (.named label))
    (hpredBlock : sourceCfg.lookup pred = some predBlock)
    (htotal : Total (M := M) source)
    (hrel : EnvRelOn (M := M) (sourceVars sourceCfg)
      (endEnv pred predBlock) source target)
    (hcoverage : ∀ x, x ∈ sourceVars sourceCfg) :
    (Isotope.TAC.Densem.Phi.Monadic.enter M target pred
        (convertBlock sourceCfg (sourceVars sourceCfg) (.named label) block) >>=
      fun result => pure
        (project (M := M) (endEnv (.named label) block) result.1, result.2)) =
      Isotope.TAC.Densem.Monadic.Block.denote M source
        (Isotope.TAC.Densem.Classical.block block) := by
  let values : ν → M.Val := fun x => Classical.choose (htotal x)
  have hvalue : ∀ x, source x = some (values x) := fun x =>
    Classical.choose_spec (htotal x)
  have ha := assignments_convert M sourceCfg (sourceVars sourceCfg) label pred
    predBlock target values hpred hpredBlock
      (fun x hx => by rw [hrel x hx, hvalue x])
  have hstart : EnvRel (M := M) (startEnv (.named label)) source
      (Isotope.TAC.Densem.Phi.Monadic.install target
        ((sourceVars sourceCfg).map fun x =>
          (Version.phi label x, values x))) := by
    intro x
    rw [installed_phi_envRelOn M (sourceVars sourceCfg)
      (sourceVars_nodup sourceCfg) label values target x (hcoverage x)]
    exact (hvalue x).symm
  unfold Isotope.TAC.Densem.Phi.Monadic.enter
  simp only [convertBlock]
  rw [ha]
  simp only [pure_bind]
  exact convertBlock_denote_project M sourceCfg (sourceVars sourceCfg)
    (.named label) block source
    (Isotope.TAC.Densem.Phi.Monadic.install target
      ((sourceVars sourceCfg).map fun x =>
        (Version.phi label x, values x))) hstart
    (Isotope.TAC.Densem.Convert.freshFor_startEnv
      (.named label) block.body)

/-- Entry-block conversion commutes monadically from the canonical external
store, including effects and failure. -/
theorem enter_entry_denote [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (sourceCfg : Isotope.TAC.Classical.CFG ν φ κ) (source : MEnv M ν) :
    (Isotope.TAC.Densem.Phi.Monadic.enter M
        (externalEnv (M := M) (κ := κ) source) .entry
        (convertBlock sourceCfg (sourceVars sourceCfg) .entry sourceCfg.entry) >>=
      fun result => pure
        (project (M := M) (endEnv .entry sourceCfg.entry) result.1, result.2)) =
      Isotope.TAC.Densem.Monadic.Block.denote M source
        (Isotope.TAC.Densem.Classical.block sourceCfg.entry) := by
  unfold Isotope.TAC.Densem.Phi.Monadic.enter
  simp only [convertBlock, Isotope.TAC.Densem.Phi.Monadic.assignments,
    pure_bind, Isotope.TAC.Densem.Phi.Monadic.install]
  exact convertBlock_denote_project M sourceCfg (sourceVars sourceCfg) .entry
    sourceCfg.entry source (externalEnv (M := M) (κ := κ) source)
    (external_envRel M source)
    (Isotope.TAC.Densem.Convert.freshFor_startEnv .entry sourceCfg.entry.body)

end Isotope.TAC.Densem.Convert.Monadic
