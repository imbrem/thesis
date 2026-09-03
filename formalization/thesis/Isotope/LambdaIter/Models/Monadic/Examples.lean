import Isotope.LambdaIter.Models.Monadic.Alg
import Isotope.LambdaIter.Models.Monadic.Free

/-!
# The partiality algebra of lambda-iter separates a loop from a value

`Alg.ofModel` at the free partiality model of the empty signature is not the
terminal algebra, and it has genuine *iteration* content: the term
`iter () (inr ·)`, a loop that never returns, denotes `Part.none`, while `()`
denotes `Part.some ()`.  Composed with soundness this says the lambda-iter
equational theory does not prove that a divergent loop equals a value — a
non-derivability result no algebra in this repository could witness before,
since every one of them was terminal, constant, or syntactic.
-/

namespace Isotope.LambdaIter.Monadic

open LocallyNameless

open Isotope.Elgot
open Isotope.LambdaIter.Monadic.SeqModel

instance : InjectiveFormers Sig.empty.{0}.Ty :=
  inferInstanceAs (InjectiveFormers (Ty EmptyBase.{0}))

/-- The body of the loop: re-enter with the same unit state. -/
abbrev loopBody : HasType Sig.empty.{0}.Instr
    (Ctx.nil : Ctx Empty Sig.empty.{0}.Ty)
    (BoundCtx.snoc BoundCtx.nil unit) (.inr (.bv 0))
    (coprod unit unit) := .inr .bv

/-- The always-looping term at the unit type: `iter () (inr ·)`. -/
abbrev loop : HasType Sig.empty.{0}.Instr
    (Ctx.nil : Ctx Empty Sig.empty.{0}.Ty) (.nil)
    (.iter .unit (.inr (.bv 0))) unit := .iter .unit loopBody

/-- The unit value. -/
abbrev unitTm : HasType Sig.empty.{0}.Instr
    (Ctx.nil : Ctx Empty Sig.empty.{0}.Ty) (.nil) .unit unit := .unit

/-- The loop diverges: it denotes the empty partial value. -/
theorem denote_loop : denote partModel loop PUnit.unit = Part.none := by
  rw [denote_iter, denote_unit, pure_bind]
  have hbody : (fun x : partModel.interp unit =>
      denote partModel loopBody (PUnit.unit, x) >>= fun s =>
        pure (partModel.coprodEquiv unit unit s)) =
      fun x => Part.some (Sum.inr x) := by
    funext x
    simp only [denote_inr, bind_assoc, pure_bind, Equiv.apply_symm_apply]
    change ((pure x : Part (partModel.interp unit)) >>=
      fun b => pure (Sum.inr b)) = Part.some (Sum.inr x)
    rw [pure_bind]
    rfl
  rw [hbody]
  exact Isotope.Elgot.Part.iter_forever _

/-- The unit value converges. -/
theorem denote_unitTm :
    denote partModel unitTm PUnit.unit = Part.some () := by
  rw [denote_unit]
  rfl

/-- **The partiality algebra of lambda-iter is not the terminal one**, and it
sees divergence: the loop and the unit value have different denotations. -/
theorem denote_loop_ne_unit :
    (Alg.ofModel partModel).denote loop ≠
      (Alg.ofModel partModel).denote unitTm := by
  intro h
  rw [ofModel_denote, ofModel_denote] at h
  have h' := congrFun h PUnit.unit
  rw [denote_loop, denote_unitTm] at h'
  exact absurd h'.symm (Part.some_ne_none ())

/-- **A non-derivability result with semantic content**: the lambda-iter
equational theory does not identify a divergent loop with a value. -/
theorem not_eqv_loop_unit :
    ¬ Eqv (Φ := Sig.empty.{0}.Instr) Sig.empty.pureEff
      (Ctx.nil : Ctx Empty Sig.empty.{0}.Ty) (.nil)
      (.iter .unit (.inr (.bv 0))) .unit unit := fun he =>
  denote_loop_ne_unit ((Alg.ofModel partModel).sound loop unitTm he)

end Isotope.LambdaIter.Monadic
