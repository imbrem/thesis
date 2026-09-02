import Isotope.LambdaSSA.Translation.Expression
import Isotope.LambdaIter.Metatheory.Typing

/-! # Reverse translation from acyclic lambda-SSA regions to lambda-iter -/

namespace Isotope.LambdaSSA.Translation.FromSSA

open Isotope
open Isotope.LambdaIter

universe u v
variable {τ : Type u} [LambdaIter.TypeFormers τ]
variable {Φ : Type v} [LambdaIter.HasTy Φ τ]

abbrev ITm (Φ : Type v) (n : Nat) := LambdaIter.LocallyNameless.Tm Empty Φ n
abbrev BCtx (τ : Type u) (n : Nat) := LambdaIter.LocallyNameless.BoundCtx τ n

/-- Turn a newest-first SSA context into the corresponding snoc context. -/
def boundContext : (Γ : LambdaSSA.VCtx τ) → BCtx τ Γ.length
  | [] => .nil
  | A :: Γ => (boundContext Γ).snoc A

@[simp] theorem expression_context_boundContext (Γ : LambdaSSA.VCtx τ) :
    LambdaSSA.Translation.Expression.context (boundContext Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => simp [boundContext, ih]

/-- The result type of a region with exits `L`: a finite right-associated
coproduct, with `empty` representing the absence of exits. -/
def labelType : LambdaSSA.LCtx τ → τ
  | [] => LambdaIter.empty
  | A :: L => LambdaIter.coprod A (labelType L)

/-- Feedback state for compiling a CFG.  The left summand is the distinguished
entry state; the right summand selects a local block and carries its argument. -/
def cfgStateType (locals : LambdaSSA.LCtx τ) : τ :=
  LambdaIter.coprod LambdaIter.unit (labelType locals)

/-- Distinguished initial state of the simultaneous iteration. -/
def cfgStart {n : Nat} : ITm Φ n := .inl .unit

/-- Embed a local-label destination into the simultaneous iteration state. -/
def cfgLocal {n : Nat} (target : ITm Φ n) : ITm Φ n := .inr target

/-- Promote local feedback into the CFG state while preserving external exits. -/
def promoteFeedback (target : ITm Φ n) : ITm Φ n :=
  .case target (.inl (.bv 0)) (.inr (cfgLocal (.bv 0)))

def promoteFeedback_hasType {externals locals : LambdaSSA.LCtx τ}
    {β : BCtx τ n} {target : ITm Φ n}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β target
        (LambdaIter.coprod (labelType externals) (labelType locals))) :
    LambdaIter.LocallyNameless.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      β (promoteFeedback target)
        (LambdaIter.coprod (labelType externals) (cfgStateType locals)) :=
  .case h (.inl .bv) (.inr (.inr .bv))

/-- Insert `k` retained dispatcher values below a block's newest parameter. -/
def insertUnderTop (k : Nat) (t : ITm Φ (n + 1)) : ITm Φ (n + k + 1) :=
  t.rename (Fin.cases 0 (fun i =>
    ⟨i.val + k + 1, by omega⟩))

/-- Append a vector of retained dispatcher types to an exact bound context. -/
def retainContext : (β : BCtx τ n) → (xs : List τ) → BCtx τ (n + xs.length)
  | β, [] => β
  | β, x :: xs => (retainContext β xs).snoc x

private theorem retainContext_get (β : BCtx τ n) (xs : List τ) (i : Fin n) :
    (retainContext β xs).get ⟨i.val + xs.length, by omega⟩ = β.get i := by
  induction xs with
  | nil => simpa [retainContext]
  | cons x xs ih => simpa [retainContext] using ih

/-- Typing specialization for inserting a vector of retained values below a
block parameter. -/
def insertUnderTop_hasType {β : BCtx τ n} {Y A : τ} {t : ITm Φ (n + 1)}
    (retained : List τ)
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) (.snoc β Y) t A) :
    LambdaIter.LocallyNameless.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (.snoc (retainContext β retained) Y)
      (insertUnderTop retained.length t) A :=
  h.rename (Fin.cases 0 (fun i => ⟨i.val + retained.length + 1, by omega⟩)) (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact retainContext_get β retained j)

/-- Eliminate a heterogeneous local-label coproduct and select its compiled
block. `retained` records the case discriminants accumulated on the path. -/
def dispatchLabels : (locals retained : List τ) →
    (Fin locals.length → ITm Φ (n + 1)) →
    ITm Φ (n + retained.length + 1)
  | [], _, _ => .abort (.bv 0)
  | head :: rest, retained, blocks =>
      .case (.bv 0)
        (insertUnderTop (retained.length + 1) (blocks 0))
        (dispatchLabels rest (labelType (head :: rest) :: retained)
          (fun i => blocks i.succ))

/-- Exact typing of finite local-label dispatch. -/
def dispatchLabels_hasType (locals retained : List τ) {β : BCtx τ n} {C : τ}
    (blocks : Fin locals.length → ITm Φ (n + 1))
    (hb : ∀ i, LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (.snoc β (locals.get i)) (blocks i) C) :
    LambdaIter.LocallyNameless.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (.snoc (retainContext β retained) (labelType locals))
      (dispatchLabels locals retained blocks) C := by
  induction locals generalizing retained with
  | nil => exact .abort .bv
  | cons head rest ih =>
      apply LambdaIter.LocallyNameless.HasType.case .bv
      · exact insertUnderTop_hasType (labelType (head :: rest) :: retained) (hb 0)
      · apply ih (retained := labelType (head :: rest) :: retained)
        intro i
        exact hb i.succ

/-- Reassociate an appended label coproduct into either an external result or
local feedback.  This is the syntactic counterpart of `labelAppendSplit` in
the categorical region semantics. -/
def routeAppend (locals externals : LambdaSSA.LCtx τ) :
    ITm Φ n → ITm Φ n :=
  match locals with
  | [] => fun target => .inl target
  | _ :: rest => fun target => .case target
      (.inr (.inl (.bv 0)))
      (.case (routeAppend rest externals (.bv 0))
        (.inl (.bv 0)) (.inr (.inr (.bv 0))))

def cfgStart_hasType {locals : LambdaSSA.LCtx τ} {β : BCtx τ n} :
    LambdaIter.LocallyNameless.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      β (cfgStart (Φ := Φ)) (cfgStateType locals) :=
  .inl .unit

def cfgLocal_hasType {locals : LambdaSSA.LCtx τ} {β : BCtx τ n} {target : ITm Φ n}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β target (labelType locals)) :
    LambdaIter.LocallyNameless.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      β (cfgLocal target) (cfgStateType locals) :=
  .inr h

/-- Typing of the appended-label routing term. -/
def routeAppend_hasType (locals externals : LambdaSSA.LCtx τ)
    {β : BCtx τ n} {target : ITm Φ n}
    (h : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β target
        (labelType (locals ++ externals))) :
    LambdaIter.LocallyNameless.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      β (routeAppend locals externals target)
        (LambdaIter.coprod (labelType externals) (labelType locals)) := by
  induction locals generalizing n β target with
  | nil => exact .inl h
  | cons A rest ih =>
      exact .case h
        (.inr (.inl (.bv (ι := 0))))
        (.case (ih (.bv (ι := 0)))
          (.inl (.bv (ι := 0)))
          (.inr (.inr (.bv (ι := 0)))))

/-- Inject the value of a selected label into the region result coproduct. -/
def injectLabel {L : LambdaSSA.LCtx τ} {A : τ} (h : LambdaSSA.At L i A)
    (a : ITm Φ n) : ITm Φ n :=
  match L, i with
  | _ :: _, 0 => .inl a
  | _ :: L, i + 1 => .inr (injectLabel (L := L) h a)

def termOfScoped {Γ : LambdaSSA.VCtx τ} {t : LambdaSSA.Tm Φ}
    (s : LambdaSSA.Translation.Expression.Scoped Γ.length t) : ITm Φ Γ.length :=
  LambdaSSA.Translation.Expression.fromSSA s

/-- The expression bridge preserves typing in the reverse direction. -/
theorem termOfScoped_hasType {Γ : LambdaSSA.VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    (h : LambdaSSA.Tm.HasType Γ t A)
    (s : LambdaSSA.Translation.Expression.Scoped Γ.length t) :
    Nonempty (LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (boundContext Γ) (termOfScoped s) A) := by
  induction h with
  | var h =>
      cases s with
      | var i =>
          have hi := LambdaSSA.Translation.Expression.getElem_context (boundContext _) i
          rw [expression_context_boundContext] at hi
          have e := Option.some.inj (hi.symm.trans h)
          exact ⟨e ▸ .bv⟩
  | op _ ih => cases s with | op s => exact (ih s).map .op
  | let₁ _ _ iha ihb =>
      cases s with | let₁ sa sb => exact ⟨.let₁ (iha sa).some (ihb sb).some⟩
  | pair _ _ iha ihb =>
      cases s with | pair sa sb => exact ⟨.pair (iha sa).some (ihb sb).some⟩
  | unit => cases s; exact ⟨.unit⟩
  | let₂ _ _ iha ihb =>
      cases s with | let₂ sa sb => exact ⟨.let₂ (iha sa).some (ihb sb).some⟩
  | inl _ ih => cases s with | inl s => exact (ih s).map .inl
  | inr _ ih => cases s with | inr s => exact (ih s).map .inr
  | case _ _ _ ihe ihl ihr =>
      cases s with | case se sl sr => exact ⟨.case (ihe se).some (ihl sl).some (ihr sr).some⟩
  | abort _ ih => cases s with | abort s => exact (ih s).map .abort

/-- Explicit evidence that a region is acyclic.  Term typing evidence is
retained so the translation is intrinsically scoped and type preserving. -/
inductive Acyclic : {Γ : LambdaSSA.VCtx τ} → {r : LambdaSSA.Region Φ} →
    {L : LambdaSSA.LCtx τ} → LambdaSSA.Region.HasType Γ r L → Type (max u v) where
  | br (h : LambdaSSA.At L i A) (ha : LambdaSSA.Tm.HasType Γ a A)
      (sa : LambdaSSA.Translation.Expression.Scoped Γ.length a) :
      Acyclic (.br h ha)
  | case (he : LambdaSSA.Tm.HasType Γ e (LambdaIter.coprod A B))
      (hl : LambdaSSA.Region.HasType (A :: Γ) l L)
      (hr : LambdaSSA.Region.HasType (B :: Γ) r L) :
      LambdaSSA.Translation.Expression.Scoped Γ.length e →
      Acyclic hl → Acyclic hr → Acyclic (.case he hl hr)
  | let₁ (ha : LambdaSSA.Tm.HasType Γ a A)
      (hr : LambdaSSA.Region.HasType (A :: Γ) r L) :
      LambdaSSA.Translation.Expression.Scoped Γ.length a →
      Acyclic hr → Acyclic (.let₁ ha hr)
  | let₂ (ha : LambdaSSA.Tm.HasType Γ a (LambdaIter.tensor A B))
      (hr : LambdaSSA.Region.HasType (B :: A :: Γ) r L) :
      LambdaSSA.Translation.Expression.Scoped Γ.length a →
      Acyclic hr → Acyclic (.let₂ ha hr)

/-- Translate an acyclic typed SSA region to an exact lambda-iter term whose
result selects one of the region's labels. -/
def toIter : {Γ : LambdaSSA.VCtx τ} → {r : LambdaSSA.Region Φ} →
    {L : LambdaSSA.LCtx τ} → {h : LambdaSSA.Region.HasType Γ r L} →
    Acyclic h → ITm Φ Γ.length
  | _, _, _, _, .br h _ sa => .let₁ (termOfScoped sa) (injectLabel h (.bv 0))
  | _, _, _, _, .case _ _ _ se al ar =>
      .case (termOfScoped se) (toIter al) (toIter ar)
  | _, _, _, _, .let₁ _ _ sa ar => .let₁ (termOfScoped sa) (toIter ar)
  | _, _, _, _, .let₂ _ _ sa ar => .let₂ (termOfScoped sa) (toIter ar)

private def injectLabel_hasType {L : LambdaSSA.LCtx τ} {A : τ}
    (h : LambdaSSA.At L i A) {β : BCtx τ n} {a : ITm Φ n}
    (ha : LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β a A) :
    LambdaIter.LocallyNameless.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      β (injectLabel h a) (labelType L) := by
  induction L generalizing i with
  | nil => simp [LambdaSSA.At] at h
  | cons B L ih =>
      cases i with
      | zero =>
          have e : B = A := by simpa [LambdaSSA.At] using h
          subst B
          exact .inl ha
      | succ i => exact .inr (ih h)

/-- Exact typing preservation for the acyclic reverse translation. -/
theorem toIter_hasType {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region Φ}
    {L : LambdaSSA.LCtx τ} {h : LambdaSSA.Region.HasType Γ r L}
    (a : Acyclic h) :
    Nonempty (LambdaIter.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (boundContext Γ) (toIter a) (labelType L)) := by
  induction a with
  | br h ha sa =>
      exact ⟨.let₁ (termOfScoped_hasType ha sa).some (injectLabel_hasType h .bv)⟩
  | case he hl hr se al ar ihl ihr =>
      exact ⟨.case (termOfScoped_hasType he se).some ihl.some ihr.some⟩
  | let₁ ha hr sa ar ih => exact ⟨.let₁ (termOfScoped_hasType ha sa).some ih.some⟩
  | let₂ ha hr sa ar ih => exact ⟨.let₂ (termOfScoped_hasType ha sa).some ih.some⟩

end Isotope.LambdaSSA.Translation.FromSSA
