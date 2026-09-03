import Isotope.LambdaCase.Models.Monadic.Alg
import Isotope.LambdaIter.Models.Monadic.Free

/-!
# The partiality algebra of lambda-case separates terms

`Alg.ofModel` at the free partiality model of the empty signature is not the
terminal algebra: it distinguishes `inl ()` from `inr ()`.  Composed with
soundness this yields a non-derivability result with genuine semantic content
— the lambda-case equational theory does not identify the two booleans —
of a kind previously unavailable, since every algebra in this repository was
terminal, constant, or syntactic.
-/

namespace Isotope.LambdaCase.Monadic

open LocallyNameless

open Isotope.LambdaIter (Sig EmptyTy EmptyBase TypeFormers)
open Isotope.LambdaIter.Monadic

/-- The booleans of the empty type universe. -/
abbrev boolT : Sig.empty.{0}.Ty :=
  TypeFormers.coprod (τ := Sig.empty.{0}.Ty) TypeFormers.unit TypeFormers.unit

instance : Isotope.LambdaIter.InjectiveFormers Sig.empty.{0}.Ty :=
  inferInstanceAs (Isotope.LambdaIter.InjectiveFormers
    (Isotope.LambdaIter.Ty EmptyBase.{0}))

/-- The typing derivation of `inl ()` at the booleans. -/
abbrev inlUnit : HasType Sig.empty.{0}.Instr
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty Sig.empty.{0}.Ty)
    (.nil) (.inl .unit) boolT := .inl .unit

/-- The typing derivation of `inr ()` at the booleans. -/
abbrev inrUnit : HasType Sig.empty.{0}.Instr
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty Sig.empty.{0}.Ty)
    (.nil) (.inr .unit) boolT := .inr .unit

/-- `inl ()` denotes the left boolean. -/
theorem denote_inlUnit :
    denote partModel inlUnit PUnit.unit = Part.some (Sum.inl ()) := by
  rw [denote_inl, denote_unit, pure_bind]
  rfl

/-- `inr ()` denotes the right boolean. -/
theorem denote_inrUnit :
    denote partModel inrUnit PUnit.unit = Part.some (Sum.inr ()) := by
  rw [denote_inr, denote_unit, pure_bind]
  rfl

/-- **The partiality algebra of lambda-case is not the terminal one**: it
separates the two booleans. -/
theorem denote_inlUnit_ne_inrUnit :
    (Alg.ofModel partModel).denote inlUnit ≠
      (Alg.ofModel partModel).denote inrUnit := by
  intro h
  rw [ofModel_denote, ofModel_denote] at h
  have h' := congrFun h PUnit.unit
  rw [denote_inlUnit, denote_inrUnit] at h'
  cases _root_.Part.some_injective h'

/-- **A non-derivability result with semantic content**: the lambda-case
equational theory does not identify the two booleans. -/
theorem not_equiv_inl_inr :
    ¬ Equiv (Φ := Sig.empty.{0}.Instr) Sig.empty.pureEff
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty Sig.empty.{0}.Ty)
      (.nil) (.inl .unit) (.inr .unit) boolT := fun he =>
  denote_inlUnit_ne_inrUnit ((Alg.ofModel partModel).sound inlUnit inrUnit he)

end Isotope.LambdaCase.Monadic
