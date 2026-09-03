import Isotope.LambdaIter.Signature.Category
import Isotope.LambdaIter.Subtyping.LocallyNameless.Typing

/-! # Proof-relevant algebraic models of lambda-iter -/

namespace Isotope.LambdaIter.Subtyping.Models

open Isotope.LambdaIter Isotope.LambdaIter.LocallyNameless

universe u w

namespace Alg

/-- Operations interpreting proof-relevant lambda-iter derivations.  In
particular, `coeSub` receives the actual subtype witness. -/
structure Ops (S : LambdaIter.Sig.{u}) [LambdaIter.Subtyping S.Ty] :
    Type (max u (w + 1)) where
  El : {n : Nat} → BoundCtx S.Ty n → S.Ty → Type w
  var : ∀ {n} {β : BoundCtx S.Ty n} (i : Fin n), El β (β.get i)
  op : ∀ {n} {β : BoundCtx S.Ty n} (f : S.Instr),
    El β (instrSrc f) → El β (instrTrg f)
  let₁ : ∀ {n} {β : BoundCtx S.Ty n} {A B}, El β A → El (β.snoc A) B → El β B
  unit : ∀ {n} {β : BoundCtx S.Ty n}, El β LambdaIter.unit
  pair : ∀ {n} {β : BoundCtx S.Ty n} {A B},
    El β A → El β B → El β (LambdaIter.tensor A B)
  let₂ : ∀ {n} {β : BoundCtx S.Ty n} {A B C},
    El β (LambdaIter.tensor A B) → El ((β.snoc A).snoc B) C → El β C
  inl : ∀ {n} {β : BoundCtx S.Ty n} {A B}, El β A → El β (LambdaIter.coprod A B)
  inr : ∀ {n} {β : BoundCtx S.Ty n} {A B}, El β B → El β (LambdaIter.coprod A B)
  case : ∀ {n} {β : BoundCtx S.Ty n} {A B C},
    El β (LambdaIter.coprod A B) → El (β.snoc A) C → El (β.snoc B) C → El β C
  abort : ∀ {n} {β : BoundCtx S.Ty n} {C}, El β LambdaIter.empty → El β C
  iter : ∀ {n} {β : BoundCtx S.Ty n} {A B},
    El β A → El (β.snoc A) (LambdaIter.coprod B A) → El β B
  coeSub : ∀ {n} {β : BoundCtx S.Ty n} {A B}, Subty A B → El β A → El β B

/-- Structural interpretation retaining all subtype evidence. -/
def Ops.denote {S : LambdaIter.Sig.{u}} [LambdaIter.Subtyping S.Ty]
    (X : Ops.{u, w} S) : {n : Nat} → {β : BoundCtx S.Ty n} →
    {t : LambdaIter.LocallyNameless.Tm Empty S.Instr n} → {A : S.Ty} →
    LambdaIter.Subtyping.LocallyNameless.HasType S.Instr Ctx.nil β t A → X.El β A
  | _, _, _, _, .fv h => absurd h (by simp [Ctx.lookup])
  | _, _, _, _, .bv (ι := i) => X.var i
  | _, _, _, _, .op (f := f) h => X.op f (X.denote h)
  | _, _, _, _, .let₁ ha hb => X.let₁ (X.denote ha) (X.denote hb)
  | _, _, _, _, .unit => X.unit
  | _, _, _, _, .pair ha hb => X.pair (X.denote ha) (X.denote hb)
  | _, _, _, _, .let₂ ha hb => X.let₂ (X.denote ha) (X.denote hb)
  | _, _, _, _, .inl h => X.inl (X.denote h)
  | _, _, _, _, .inr h => X.inr (X.denote h)
  | _, _, _, _, .case he hl hr => X.case (X.denote he) (X.denote hl) (X.denote hr)
  | _, _, _, _, .abort h => X.abort (X.denote h)
  | _, _, _, _, .iter ha hb => X.iter (X.denote ha) (X.denote hb)
  | _, _, _, _, .sub h d => X.coeSub d (X.denote h)

end Alg

/-- A proof-relevant model.  No witness equality is imposed by default. -/
structure Alg (S : LambdaIter.Sig.{u}) [LambdaIter.Subtyping S.Ty]
    extends Alg.Ops.{u, w} S

namespace Alg

variable {S : LambdaIter.Sig.{u}} [LambdaIter.Subtyping S.Ty]

abbrev denote (X : Alg.{u, w} S) {n} {β : BoundCtx S.Ty n}
    {t : LambdaIter.LocallyNameless.Tm Empty S.Instr n} {A}
    (h : LambdaIter.Subtyping.LocallyNameless.HasType S.Instr Ctx.nil β t A) :
    X.El β A := X.toOps.denote h

/-- Optional semantic proof irrelevance.  Refinement developments that care
about coercion paths deliberately do not assume this class. -/
class WitnessCoherent (X : Alg.{u, w} S) : Prop where
  denote_eq {n} {β : BoundCtx S.Ty n} {t : LambdaIter.LocallyNameless.Tm Empty S.Instr n}
    {A} (h k : LambdaIter.Subtyping.LocallyNameless.HasType S.Instr Ctx.nil β t A) :
    X.denote h = X.denote k

theorem denote_sub (X : Alg.{u, w} S) {n} {β : BoundCtx S.Ty n}
    {t : LambdaIter.LocallyNameless.Tm Empty S.Instr n} {A B}
    (h : LambdaIter.Subtyping.LocallyNameless.HasType S.Instr Ctx.nil β t A)
    (d : Subty A B) : X.denote (.sub h d) = X.coeSub d (X.denote h) := rfl

end Alg
end Isotope.LambdaIter.Subtyping.Models
