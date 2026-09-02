import Isotope.TAC.Dominator.Foundation
import Isotope.TAC.Classical.WellFormed

namespace Isotope.TAC.Dominator

universe u v w

open Isotope.TAC

variable {Var : Type u} {Op : Type v} {Label : Type w} [DecidableEq Label]

/-- Forget instructions and retain the classical CFG's control-flow graph. -/
def ofClassical (cfg : Classical.CFG Var Op Label) : CFG (Classical.BlockId Label) where
  entry := .entry
  edge a b := b ∈ cfg.successors a

theorem Classical.CFG.Path.toDominator_exists {cfg : Classical.CFG Var Op Label}
    {a b : Classical.BlockId Label} {xs : List (Classical.BlockId Label)}
    (p : Classical.CFG.Path cfg a xs b) :
    ∃ q : (ofClassical cfg).Path a b,
      ∀ d, CFG.Path.Contains (ofClassical cfg) d q → d ∈ xs := by
  induction p with
  | single a =>
      refine ⟨.nil a, ?_⟩
      intro d h
      cases h
      simp
  | step h p ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨.cons h q, ?_⟩
      intro d hd
      cases hd with
      | head => simp
      | tail hd => exact List.mem_cons_of_mem _ (hq _ hd)

theorem Classical.CFG.dominates_of_dominator
    {cfg : Classical.CFG Var Op Label} {d b : Classical.BlockId Label}
    (h : CFG.Dominates (ofClassical cfg) d b) : cfg.Dominates d b := by
  intro xs p
  rcases Classical.CFG.Path.toDominator_exists p with ⟨q, hq⟩
  exact hq _ (h q)

theorem dominatorPath_toClassical_exists {cfg : Classical.CFG Var Op Label}
    {a b : Classical.BlockId Label} (q : (ofClassical cfg).Path a b) :
    ∃ xs, Classical.CFG.Path cfg a xs b ∧
      ∀ d, d ∈ xs → CFG.Path.Contains (ofClassical cfg) d q := by
  induction q with
  | nil a =>
      refine ⟨[a], .single a, ?_⟩
      intro d hd
      simp only [List.mem_singleton] at hd
      subst d
      exact .head _
  | cons e q ih =>
      rcases ih with ⟨xs, p, hp⟩
      refine ⟨_ :: xs, .step e p, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact .head _
      · exact .tail (hp _ hd)

theorem dominator_of_Classical_dominates
    {cfg : Classical.CFG Var Op Label} {d b : Classical.BlockId Label}
    (h : cfg.Dominates d b) : CFG.Dominates (ofClassical cfg) d b := by
  intro q
  rcases dominatorPath_toClassical_exists q with ⟨xs, p, hp⟩
  exact hp _ (h xs p)

theorem Classical_dominates_iff_dominator
    {cfg : Classical.CFG Var Op Label} {d b : Classical.BlockId Label} :
    cfg.Dominates d b ↔ CFG.Dominates (ofClassical cfg) d b :=
  ⟨dominator_of_Classical_dominates, Classical.CFG.dominates_of_dominator⟩

/-- A classical lexical scope selected through any valid explicit dominator
tree agrees with graph dominance and is therefore choice-independent. -/
theorem classical_scope_choice_independent
    {cfg : Classical.CFG Var Op Label}
    (T U : DominatorTree (ofClassical cfg)) : T.Equivalent U :=
  DominatorTree.equivalent_of_spec T U

end Isotope.TAC.Dominator
