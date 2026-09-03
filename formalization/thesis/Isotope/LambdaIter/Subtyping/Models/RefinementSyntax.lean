import Isotope.LambdaIter.Subtyping.Models.Refinement
import Isotope.LambdaIter.Subtyping.LocallyNameless.RefinementOrder

/-! # The syntactic ordered model and refinement completeness -/

namespace Isotope.LambdaIter.Subtyping.Models

open Isotope.LambdaIter Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless.Refinement

universe u

variable {S : LambdaIter.Sig.{u}} [LambdaIter.Subtyping S.Ty]

/-- The initial syntactic preorder: elements are raw terms equipped with their
exact typing derivations, ordered by generated refinement. -/
def refinementSyntax
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) : Alg S where
  El β A := Presentation S.pureEff Ctx.nil R β A
  var i := ⟨.bv i, .bv⟩
  op f a := ⟨.op f a.term, .op a.typing⟩
  let₁ a b := ⟨.let₁ a.term b.term, .let₁ a.typing b.typing⟩
  unit := ⟨.unit, .unit⟩
  pair a b := ⟨.pair a.term b.term, .pair a.typing b.typing⟩
  let₂ a c := ⟨.let₂ a.term c.term, .let₂ a.typing c.typing⟩
  inl a := ⟨.inl a.term, .inl a.typing⟩
  inr b := ⟨.inr b.term, .inr b.typing⟩
  case e l r := ⟨.case e.term l.term r.term, .case e.typing l.typing r.typing⟩
  abort a := ⟨.abort a.term, .abort a.typing⟩
  iter a b := ⟨.iter a.term b.term, .iter a.typing b.typing⟩
  coeSub d a := ⟨a.term, .sub a.typing d⟩

theorem refinementSyntax_denote
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty))
    {h : HasType S.Instr Ctx.nil β t A} :
    (refinementSyntax R).denote h = ⟨t, h⟩ := by
  induction h with
  | fv h => simp [Ctx.lookup] at h
  | _ => simp_all [Alg.denote, Alg.Ops.denote, refinementSyntax]

instance refinementSyntax_lawfulOrder
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    LawfulOrder (refinementSyntax R) where
  le := fun _ _ a b => Related S.pureEff Ctx.nil R a.typing b.typing
  le_refl a := Related.refl a.typing
  le_trans h k := h.trans k
  op_mono _ := Related.op
  let₁_mono := Related.let₁
  pair_mono := Related.pair
  let₂_mono := Related.let₂
  inl_mono := Related.inl
  inr_mono := Related.inr
  case_mono := Related.case
  abort_mono := Related.abort
  iter_mono := Related.iter
  coeSub_mono := fun d _ _ h => Related.sub h d
  equiv_sound := by
    intro n β a b A ha hb h
    rw [refinementSyntax_denote, refinementSyntax_denote]
    exact Related.ofEquiv ⟨h⟩

theorem refinementSyntax_validates
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    LawfulOrder.Validates (refinementSyntax R) R := by
  intro n β a b A ha hb h
  rw [refinementSyntax_denote, refinementSyntax_denote]
  change Related S.pureEff Ctx.nil R ha hb
  exact Related.axiom h

/-- Completeness: semantic ordering in the syntactic model is precisely
derivable refinement. -/
theorem refinement_complete
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty))
    {ha : HasType S.Instr Ctx.nil β a A}
    {hb : HasType S.Instr Ctx.nil β b A}
    (h : LawfulOrder.le β A
      ((refinementSyntax R).denote ha) ((refinementSyntax R).denote hb)) :
    Related S.pureEff Ctx.nil R ha hb := by
  rw [refinementSyntax_denote, refinementSyntax_denote] at h
  change Related S.pureEff Ctx.nil R ha hb at h
  exact h

/-- Soundness and completeness combine to characterize generated refinement
as validity in its initial ordered syntactic model. -/
theorem refinement_iff_syntax_le
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty))
    {ha : HasType S.Instr Ctx.nil β a A}
    {hb : HasType S.Instr Ctx.nil β b A} :
    Related S.pureEff Ctx.nil R ha hb ↔
      LawfulOrder.le β A
        ((refinementSyntax R).denote ha) ((refinementSyntax R).denote hb) := by
  rw [refinementSyntax_denote, refinementSyntax_denote]
  change Related S.pureEff Ctx.nil R ha hb ↔ Related S.pureEff Ctx.nil R ha hb
  rfl

end Isotope.LambdaIter.Subtyping.Models
