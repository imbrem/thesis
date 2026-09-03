import Isotope.LambdaIter.Subtyping.Models.Alg
import Isotope.LambdaIter.Subtyping.LocallyNameless.Refinement

/-! Ordered proof-relevant algebras and semantic validation of refinement. -/

namespace Isotope.LambdaIter.Subtyping.Models

open Isotope.LambdaIter Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless.Refinement

universe u w

variable {S : LambdaIter.Sig.{u}} [LambdaIter.Subtyping S.Ty]

private def let₂At (X : Alg.{u, w} S) {n} (β : BoundCtx S.Ty n)
    (A B C : S.Ty) (a : X.El β (LambdaIter.tensor A B))
    (c : X.El ((β.snoc A).snoc B) C) : X.El β C :=
  X.toOps.let₂ a c

/-- A proof-relevant algebra whose operations are monotone.  Equality soundness
for the typed equational theory is explicit and does not identify subtype
witnesses globally. -/
class LawfulOrder (X : Alg.{u, w} S) where
  le : ∀ {n} (β : BoundCtx S.Ty n) (A : S.Ty), X.El β A → X.El β A → Prop
  le_refl : ∀ {n β A} (x : X.El (n := n) β A), le β A x x
  le_trans : ∀ {n β A} {x y z : X.El (n := n) β A}, le β A x y → le β A y z → le β A x z
  op_mono : ∀ {n β} (f : S.Instr) {x y : X.El (n := n) β (instrSrc f)},
    le β _ x y → le β _ (X.op f x) (X.op f y)
  let₁_mono : ∀ {n β A B} {a a' : X.El (n := n) β A} {b b' : X.El (β.snoc A) B},
    le β A a a' → le (β.snoc A) B b b' → le β B (X.let₁ a b) (X.let₁ a' b')
  pair_mono : ∀ {n β A B} {a a' : X.El (n := n) β A} {b b' : X.El β B},
    le β A a a' → le β B b b' → le β _ (X.pair a b) (X.pair a' b')
  let₂_mono : ∀ {n} {β : BoundCtx S.Ty n} {A B C : S.Ty}
      {a : X.El β (LambdaIter.tensor A B)} {a' : X.El β (LambdaIter.tensor A B)}
      {c : X.El ((β.snoc A).snoc B) C}
      {c' : X.El ((β.snoc A).snoc B) C},
    le β (LambdaIter.tensor A B) a a' → le ((β.snoc A).snoc B) C c c' →
      le β C (let₂At X β A B C a c) (let₂At X β A B C a' c')
  inl_mono : ∀ {n β A B} {a a' : X.El (n := n) β A}, le β A a a' → le β _ (X.inl (B := B) a) (X.inl a')
  inr_mono : ∀ {n β A B} {b b' : X.El (n := n) β B}, le β B b b' → le β _ (X.inr (A := A) b) (X.inr b')
  case_mono : ∀ {n β A B C} {e : X.El (n := n) β (LambdaIter.coprod A B)}
      {e' : X.El (n := n) β (LambdaIter.coprod A B)}
      {l l' : X.El (β.snoc A) C} {r r' : X.El (β.snoc B) C},
    le β _ e e' → le (β.snoc A) C l l' → le (β.snoc B) C r r' →
      le β C (X.toOps.case (A := A) (B := B) e l r)
        (X.toOps.case (A := A) (B := B) e' l' r')
  abort_mono : ∀ {n β C} {a b : X.El (n := n) β LambdaIter.empty}, le β LambdaIter.empty a b → le β C (X.abort a) (X.abort b)
  iter_mono : ∀ {n β A B} {a a' : X.El (n := n) β A}
      {b b' : X.El (β.snoc A) (LambdaIter.coprod B A)},
    le β A a a' → le (β.snoc A) _ b b' → le β B (X.iter a b) (X.iter a' b')
  coeSub_mono : ∀ {n β A B} (d : Subty A B) {a a' : X.El (n := n) β A},
    le β A a a' → le β B (X.coeSub d a) (X.coeSub d a')
  equiv_sound : ∀ {n} {β : BoundCtx S.Ty n}
      {a b : LambdaIter.LocallyNameless.Tm Empty S.Instr n} {A : S.Ty}
      {ha : HasType S.Instr Ctx.nil β a A}
      {hb : HasType S.Instr Ctx.nil β b A},
    TypedEquiv.Deriv S.pureEff Ctx.nil ha hb →
      le β A (X.denote ha) (X.denote hb)

namespace LawfulOrder

variable {S : LambdaIter.Sig.{u}} [LambdaIter.Subtyping S.Ty]

def Validates (X : Alg.{u, w} S) [LawfulOrder X]
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) : Prop :=
  ∀ {n} {β : BoundCtx S.Ty n}
    {a b : LambdaIter.LocallyNameless.Tm Empty S.Instr n} {A : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil β b A), R.rel ha hb →
      LawfulOrder.le β A (X.denote ha) (X.denote hb)

theorem sound (X : Alg.{u, w} S) [LawfulOrder X] {R} (hR : Validates X R) :
    ∀ {n} {β : BoundCtx S.Ty n}
      {a b : LambdaIter.LocallyNameless.Tm Empty S.Instr n} {A : S.Ty}
      {ha : HasType S.Instr Ctx.nil β a A}
      {hb : HasType S.Instr Ctx.nil β b A},
      Deriv S.pureEff Ctx.nil R ha hb →
        LawfulOrder.le β A (X.denote ha) (X.denote hb)
  | _, _, _, _, _, _, _, .refl _ => LawfulOrder.le_refl _
  | _, _, _, _, _, _, _, .trans h k => LawfulOrder.le_trans (sound X hR h) (sound X hR k)
  | _, _, _, _, _, ha, hb, .axiom h => hR ha hb h
  | _, _, _, _, _, _, _, .equiv h => LawfulOrder.equiv_sound h
  | _, _, _, _, _, _, _, .sub h d => LawfulOrder.coeSub_mono d (sound X hR h)
  | _, _, _, _, _, _, _, .op h => LawfulOrder.op_mono _ (sound X hR h)
  | _, _, _, _, _, _, _, .let₁ h k => LawfulOrder.let₁_mono (sound X hR h) (sound X hR k)
  | _, _, _, _, _, _, _, .pair h k => LawfulOrder.pair_mono (sound X hR h) (sound X hR k)
  | _, _, _, _, _, _, _, .let₂ h k =>
      LawfulOrder.let₂_mono (sound X hR h) (sound X hR k)
  | _, _, _, _, _, _, _, .inl h => LawfulOrder.inl_mono (sound X hR h)
  | _, _, _, _, _, _, _, .inr h => LawfulOrder.inr_mono (sound X hR h)
  | _, _, _, _, _, _, _, .case h l r => LawfulOrder.case_mono (sound X hR h) (sound X hR l) (sound X hR r)
  | _, _, _, _, _, _, _, .abort h => LawfulOrder.abort_mono (sound X hR h)
  | _, _, _, _, _, _, _, .iter h k => LawfulOrder.iter_mono (sound X hR h) (sound X hR k)

end LawfulOrder
end Isotope.LambdaIter.Subtyping.Models
