import Isotope.LambdaSSA.Translation.Expression

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
