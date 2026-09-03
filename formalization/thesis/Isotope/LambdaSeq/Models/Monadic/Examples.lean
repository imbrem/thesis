import Isotope.LambdaSeq.Models.Monadic.Alg
import Isotope.LambdaIter.Models.Monadic.Free

/-!
# A concrete lambda-seq algebra: the partiality monad over the empty signature

`Alg.ofSeqModel` is only interesting if some instance of it is not the terminal
algebra.  This file exhibits one, reusing the free partiality model of
`Isotope/LambdaIter/Models/Monadic/Free.lean` (a `Model` restricts to a
`SeqModel`, which is all lambda-seq consumes): two bound variables whose
denotations differ in it.

Since the empty signature has no instructions, the model uses no data beyond
the type interpretation; the separation comes from the carrier alone, and would
survive replacing `Part` by any monad whose `pure` is injective.
-/

namespace Isotope.LambdaSeq.Monadic

open LocallyNameless

open Isotope.LambdaIter (Sig EmptyTy)
open Isotope.LambdaIter.Monadic
open Isotope.LambdaIter.Monadic.SeqModel

/-- The lambda-seq part of the free partiality model of the empty signature. -/
abbrev partSeqModel : SeqModel.{0, 0} Isotope.LambdaIter.Sig.empty.{0} Part :=
  partModel.toSeqModel

/-- The two-slot bound context of booleans. -/
def boolPair : BoundCtx EmptyTy.{0} 2 :=
  (.snoc (.snoc .nil Isotope.LambdaIter.Monadic.boolTy)
    Isotope.LambdaIter.Monadic.boolTy)

/-- **The partiality algebra of lambda-seq is not the terminal one**: the two
bound variables of `boolPair` have different denotations in it.  Hence
`Alg.ofSeqModel` produces algebras with genuine semantic content, and the two
variables are not identified by the lambda-seq equational theory. -/
theorem var_ne_var :
    (Alg.ofSeqModel partSeqModel).var (β := boolPair) 0 ≠
      (Alg.ofSeqModel partSeqModel).var (β := boolPair) 1 := by
  intro h
  have h' : (Part.some (Sum.inr () : Unit ⊕ Unit)) = Part.some (Sum.inl ()) :=
    congrArg
      (fun F => F (((PUnit.unit, Sum.inl ()), Sum.inr ()) :
        partSeqModel.Env boolPair)) h
  cases _root_.Part.some_injective h'

end Isotope.LambdaSeq.Monadic
