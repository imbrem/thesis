import Isotope.LambdaIter.Typing
import Isotope.LambdaSSA.Typing

/-!
# Translation of iteration-free lambda-iter expressions

The locally nameless lambda-iter bound context and the SSA value context both
put the newest binder at index zero.  This file exploits that exact match for
terms with no free names and no `iter` node.
-/

namespace Isotope.LambdaSSA.Translation.Expression

universe u v

variable {Φ : Type v}

/-- The newest-first list corresponding to a lambda-iter bound context. -/
def context :
    Isotope.LambdaIter.LocallyNameless.BoundCtx τ n → List τ
  | .nil => []
  | .snoc β A => A :: context β

@[simp] theorem context_nil :
    context (Isotope.LambdaIter.LocallyNameless.BoundCtx.nil :
      Isotope.LambdaIter.LocallyNameless.BoundCtx τ 0) = [] := rfl

@[simp] theorem context_snoc
    (β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n) (A : τ) :
    context (β.snoc A) = A :: context β := rfl

@[simp] theorem getElem_context
    (β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n) (i : Fin n) :
    (context β)[i.1]? = some (β.get i) := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa [context, Isotope.LambdaIter.LocallyNameless.BoundCtx.get] using ih j

/-- Iteration-free, free-name-free lambda-iter expressions. -/
inductive NoIter : {n : Nat} →
    Isotope.LambdaIter.LocallyNameless.Tm Empty Φ n → Type v where
  | bv (i : Fin n) : NoIter (.bv i)
  | op : NoIter a → NoIter (.op f a)
  | let₁ : NoIter a → NoIter b → NoIter (.let₁ a b)
  | unit : NoIter (.unit : Isotope.LambdaIter.LocallyNameless.Tm Empty Φ n)
  | pair : NoIter a → NoIter b → NoIter (.pair a b)
  | let₂ : NoIter a → NoIter b → NoIter (.let₂ a b)
  | inl : NoIter a → NoIter (.inl a)
  | inr : NoIter a → NoIter (.inr a)
  | case : NoIter e → NoIter l → NoIter r → NoIter (.case e l r)
  | abort : NoIter a → NoIter (.abort a)

/-- Erase the finite bound-variable indices of an iteration-free expression. -/
def toSSA : {t : Isotope.LambdaIter.LocallyNameless.Tm Empty Φ n} →
    NoIter t → Isotope.LambdaSSA.Tm Φ
  | _, .bv i => .var i
  | _, .op (f := f) h => .op f (toSSA h)
  | _, .let₁ ha hb => .let₁ (toSSA ha) (toSSA hb)
  | _, .unit => .unit
  | _, .pair ha hb => .pair (toSSA ha) (toSSA hb)
  | _, .let₂ ha hb => .let₂ (toSSA ha) (toSSA hb)
  | _, .inl h => .inl (toSSA h)
  | _, .inr h => .inr (toSSA h)
  | _, .case he hl hr => .case (toSSA he) (toSSA hl) (toSSA hr)
  | _, .abort h => .abort (toSSA h)

/-- An SSA expression whose variables are all in a context of size `n`.
The finite index is retained as evidence, making the reverse translation total. -/
inductive Scoped : Nat → Isotope.LambdaSSA.Tm Φ → Type v where
  | var (i : Fin n) : Scoped n (.var i)
  | op : Scoped n a → Scoped n (.op f a)
  | let₁ : Scoped n a → Scoped (n + 1) b → Scoped n (.let₁ a b)
  | pair : Scoped n a → Scoped n b → Scoped n (.pair a b)
  | unit : Scoped n .unit
  | let₂ : Scoped n a → Scoped (n + 2) b → Scoped n (.let₂ a b)
  | inl : Scoped n a → Scoped n (.inl a)
  | inr : Scoped n a → Scoped n (.inr a)
  | case : Scoped n a → Scoped (n + 1) l → Scoped (n + 1) r → Scoped n (.case a l r)
  | abort : Scoped n a → Scoped n (.abort a)

/-- Reconstruct a locally nameless expression from a scoped SSA expression. -/
def fromSSA : {t : Isotope.LambdaSSA.Tm Φ} → Scoped n t →
    Isotope.LambdaIter.LocallyNameless.Tm Empty Φ n
  | _, .var i => .bv i
  | _, .op (f := f) h => .op f (fromSSA h)
  | _, .let₁ ha hb => .let₁ (fromSSA ha) (fromSSA hb)
  | _, .pair ha hb => .pair (fromSSA ha) (fromSSA hb)
  | _, .unit => .unit
  | _, .let₂ ha hb => .let₂ (fromSSA ha) (fromSSA hb)
  | _, .inl h => .inl (fromSSA h)
  | _, .inr h => .inr (fromSSA h)
  | _, .case ha hl hr => .case (fromSSA ha) (fromSSA hl) (fromSSA hr)
  | _, .abort h => .abort (fromSSA h)

/-- The reverse translation always lands in the iteration-free fragment. -/
def fromSSA_noIter : {t : Isotope.LambdaSSA.Tm Φ} →
    (h : Scoped n t) → NoIter (fromSSA h)
  | _, .var _ => .bv _
  | _, .op h => .op (fromSSA_noIter h)
  | _, .let₁ ha hb => .let₁ (fromSSA_noIter ha) (fromSSA_noIter hb)
  | _, .pair ha hb => .pair (fromSSA_noIter ha) (fromSSA_noIter hb)
  | _, .unit => .unit
  | _, .let₂ ha hb => .let₂ (fromSSA_noIter ha) (fromSSA_noIter hb)
  | _, .inl h => .inl (fromSSA_noIter h)
  | _, .inr h => .inr (fromSSA_noIter h)
  | _, .case ha hl hr => .case (fromSSA_noIter ha) (fromSSA_noIter hl) (fromSSA_noIter hr)
  | _, .abort h => .abort (fromSSA_noIter h)

/-- Translating a scoped SSA expression to lambda-iter and back is exact. -/
@[simp] theorem toSSA_fromSSA : {t : Isotope.LambdaSSA.Tm Φ} → (h : Scoped n t) →
    toSSA (fromSSA_noIter h) = t
  | _, .var _ => rfl
  | _, .op h => by simp [toSSA, fromSSA, fromSSA_noIter, toSSA_fromSSA h]
  | _, .let₁ ha hb => by simp [toSSA, fromSSA, fromSSA_noIter, toSSA_fromSSA ha, toSSA_fromSSA hb]
  | _, .pair ha hb => by simp [toSSA, fromSSA, fromSSA_noIter, toSSA_fromSSA ha, toSSA_fromSSA hb]
  | _, .unit => rfl
  | _, .let₂ ha hb => by simp [toSSA, fromSSA, fromSSA_noIter, toSSA_fromSSA ha, toSSA_fromSSA hb]
  | _, .inl h => by simp [toSSA, fromSSA, fromSSA_noIter, toSSA_fromSSA h]
  | _, .inr h => by simp [toSSA, fromSSA, fromSSA_noIter, toSSA_fromSSA h]
  | _, .case ha hl hr => by
      simp [toSSA, fromSSA, fromSSA_noIter, toSSA_fromSSA ha, toSSA_fromSSA hl, toSSA_fromSSA hr]
  | _, .abort h => by simp [toSSA, fromSSA, fromSSA_noIter, toSSA_fromSSA h]

/-- Exact typing is preserved by erasing finite indices to SSA indices. -/
def hasType_toSSA {τ : Type u} [Isotope.LambdaIter.TypeFormers τ]
    {Φ : Type v} [Isotope.LambdaIter.HasTy Φ τ]
    {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaIter.LocallyNameless.HasType Φ
      (Isotope.LambdaIter.Ctx.nil : Isotope.LambdaIter.Ctx Empty τ) β t A)
    (hn : NoIter t) : Isotope.LambdaSSA.Tm.HasType (context β) (toSSA hn) A := by
  induction h with
  | fv h => cases h
  | bv =>
      cases hn
      exact Isotope.LambdaSSA.Tm.HasType.var (getElem_context _ _)
  | op _ ih => cases hn with | op hn => exact Isotope.LambdaSSA.Tm.HasType.op (ih hn)
  | let₁ _ _ iha ihb =>
      cases hn with | let₁ ha hb => exact Isotope.LambdaSSA.Tm.HasType.let₁ (iha ha) (ihb hb)
  | unit => cases hn; exact Isotope.LambdaSSA.Tm.HasType.unit
  | pair _ _ iha ihb =>
      cases hn with | pair ha hb => exact Isotope.LambdaSSA.Tm.HasType.pair (iha ha) (ihb hb)
  | let₂ _ _ iha ihb =>
      cases hn with | let₂ ha hb => exact Isotope.LambdaSSA.Tm.HasType.let₂ (iha ha) (ihb hb)
  | inl _ ih => cases hn with | inl hn => exact Isotope.LambdaSSA.Tm.HasType.inl (ih hn)
  | inr _ ih => cases hn with | inr hn => exact Isotope.LambdaSSA.Tm.HasType.inr (ih hn)
  | case _ _ _ ihe ihl ihr =>
      cases hn with
      | case he hl hr => exact Isotope.LambdaSSA.Tm.HasType.case (ihe he) (ihl hl) (ihr hr)
  | abort _ ih =>
      cases hn with | abort hn => exact Isotope.LambdaSSA.Tm.HasType.abort (ih hn)
  | iter => cases hn

end Isotope.LambdaSSA.Translation.Expression
