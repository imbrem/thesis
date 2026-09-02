import Isotope.LambdaIter.NoSubtyping.Typing
import Isotope.LambdaIter.Subtyping.Minimal

/-!
# Explicit minimal-subtyping coercions in the no-subtyping core

`MinimalTy.Witness` is intentionally propositionally truncated.  Lean cannot
eliminate it into term syntax, and doing so would be incoherent at the raw
syntax level.  This module therefore records an explicit, proof-relevant
derivation before erasing it to `MinimalTy.Le`.
-/

namespace Isotope.LambdaIter

namespace MinimalTy

/-- Explicit derivations for the minimal preorder.  These contain exactly the
same generators as `Le`, but live in `Type` so they can drive elaboration. -/
inductive Derivation {α : Type u} : MinimalTy α → MinimalTy α → Type u where
  | refl (A) : Derivation A A
  | trans : Derivation A B → Derivation B C → Derivation A C
  | tensor : Derivation A A' → Derivation B B' →
      Derivation (LambdaIter.tensor A B) (LambdaIter.tensor A' B')
  | coprod : Derivation A A' → Derivation B B' →
      Derivation (LambdaIter.coprod A B) (LambdaIter.coprod A' B')
  | empty (A) : Derivation LambdaIter.empty A
  | unit (A) : Derivation A LambdaIter.unit

/-- Forget the computational choice of coercion and retain only the minimal
subtyping proposition. -/
def Derivation.toLe : Derivation A B → Le A B
  | Derivation.refl A => Le.refl A
  | Derivation.trans f g => Le.trans f.toLe g.toLe
  | Derivation.tensor f g => Le.tensor f.toLe g.toLe
  | Derivation.coprod f g => Le.coprod f.toLe g.toLe
  | Derivation.empty A => Le.empty A
  | Derivation.unit A => Le.unit A

/-- Erasure into the `Subtyping` witness used by the existing generic core. -/
def Derivation.toWitness (d : Derivation A B) : Subty A B := ⟨⟨d.toLe⟩⟩

end MinimalTy

namespace NoSubtyping.LocallyNameless

open Isotope.LambdaIter.LocallyNameless

variable {α : Type u} {ν : Type w} {Φ : Type q}
variable [DecidableEq ν] [HasTy Φ (MinimalTy α)]

/-- Elaborate an explicit minimal-subtyping derivation as ordinary lambda-iter
syntax.  Empty coercions use `abort`; top coercions evaluate and discard their
argument before returning `unit`.  Tensor and coproduct coercions are mapped
componentwise. -/
def coeTm {n : Nat} {A B : MinimalTy α} :
    MinimalTy.Derivation A B → Tm ν Φ n → Tm ν Φ n
  | MinimalTy.Derivation.refl _, a => a
  | MinimalTy.Derivation.trans f g, a => coeTm g (coeTm f a)
  | MinimalTy.Derivation.tensor f g, a =>
      .let₂ a (.pair (coeTm f (.bv 1)) (coeTm g (.bv 0)))
  | MinimalTy.Derivation.coprod f g, a =>
      .case a (.inl (coeTm f (.bv 0))) (.inr (coeTm g (.bv 0)))
  | MinimalTy.Derivation.empty _, a => .abort a
  | MinimalTy.Derivation.unit _, a => .let₁ a .unit

@[simp] theorem coeTm_refl (a : Tm ν Φ n) :
    coeTm (MinimalTy.Derivation.refl A) a = a := rfl

@[simp] theorem coeTm_trans (f : MinimalTy.Derivation A B)
    (g : MinimalTy.Derivation B C) (a : Tm ν Φ n) :
    coeTm (MinimalTy.Derivation.trans f g) a = coeTm g (coeTm f a) := rfl

@[simp] theorem coeTm_tensor (f : MinimalTy.Derivation A A')
    (g : MinimalTy.Derivation B B') (a : Tm ν Φ n) :
    coeTm (MinimalTy.Derivation.tensor f g) a =
      .let₂ a (.pair (coeTm f (.bv 1)) (coeTm g (.bv 0))) := rfl

@[simp] theorem coeTm_coprod (f : MinimalTy.Derivation A A')
    (g : MinimalTy.Derivation B B') (a : Tm ν Φ n) :
    coeTm (MinimalTy.Derivation.coprod f g) a =
      .case a (.inl (coeTm f (.bv 0))) (.inr (coeTm g (.bv 0))) := rfl

/-- Every explicit coercion elaborates to a well-typed term in the core with
no subtyping rule. -/
def coeTm_hasType {Γ : Ctx ν (MinimalTy α)} {n : Nat}
    {β : BoundCtx (MinimalTy α) n} {a : Tm ν Φ n}
    {A B : MinimalTy α} (d : MinimalTy.Derivation A B)
    (ha : HasType Φ Γ β a A) : HasType Φ Γ β (coeTm d a) B :=
  match d with
  | MinimalTy.Derivation.refl _ => ha
  | MinimalTy.Derivation.trans f g =>
      coeTm_hasType g (coeTm_hasType f ha)
  | MinimalTy.Derivation.tensor f g =>
      .let₂ ha (.pair (coeTm_hasType f .bv) (coeTm_hasType g .bv))
  | MinimalTy.Derivation.coprod f g =>
      .case ha (.inl (coeTm_hasType f .bv)) (.inr (coeTm_hasType g .bv))
  | MinimalTy.Derivation.empty _ => .abort ha
  | MinimalTy.Derivation.unit _ => .let₁ ha .unit

/-- The existing typing judgment with every use of minimal subtyping supplied
as an explicit derivation.  This is the smallest extra annotation needed for
a computational elaboration into the no-subtyping core. -/
inductive AnnotatedHasType (Φ : Type q) [HasTy Φ (MinimalTy α)]
    (Γ : Ctx ν (MinimalTy α)) : {n : Nat} →
    BoundCtx (MinimalTy α) n → Tm ν Φ n → MinimalTy α → Type (max u q w) where
  | fv (h : Γ.lookup x = some A) : AnnotatedHasType Φ Γ β (.fv x) A
  | bv : AnnotatedHasType Φ Γ β (.bv i) (β.get i)
  | op (ha : AnnotatedHasType Φ Γ β a (instrSrc f)) :
      AnnotatedHasType Φ Γ β (.op f a) (instrTrg f)
  | let₁ (ha : AnnotatedHasType Φ Γ β a A)
      (hb : AnnotatedHasType Φ Γ (.snoc β A) b B) :
      AnnotatedHasType Φ Γ β (.let₁ a b) B
  | unit : AnnotatedHasType Φ Γ β .unit LambdaIter.unit
  | pair (ha : AnnotatedHasType Φ Γ β a A)
      (hb : AnnotatedHasType Φ Γ β b B) :
      AnnotatedHasType Φ Γ β (.pair a b) (LambdaIter.tensor A B)
  | let₂ (ha : AnnotatedHasType Φ Γ β a (LambdaIter.tensor A B))
      (hc : AnnotatedHasType Φ Γ (.snoc (.snoc β A) B) c C) :
      AnnotatedHasType Φ Γ β (.let₂ a c) C
  | inl (ha : AnnotatedHasType Φ Γ β a A) :
      AnnotatedHasType Φ Γ β (.inl a) (LambdaIter.coprod A B)
  | inr (hb : AnnotatedHasType Φ Γ β b B) :
      AnnotatedHasType Φ Γ β (.inr b) (LambdaIter.coprod A B)
  | case (he : AnnotatedHasType Φ Γ β e (LambdaIter.coprod A B))
      (hl : AnnotatedHasType Φ Γ (.snoc β A) l C)
      (hr : AnnotatedHasType Φ Γ (.snoc β B) r C) :
      AnnotatedHasType Φ Γ β (.case e l r) C
  | abort (ha : AnnotatedHasType Φ Γ β a LambdaIter.empty) :
      AnnotatedHasType Φ Γ β (.abort a) C
  | iter (ha : AnnotatedHasType Φ Γ β a A)
      (hb : AnnotatedHasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)) :
      AnnotatedHasType Φ Γ β (.iter a b) B
  | sub (ha : AnnotatedHasType Φ Γ β a A) (d : MinimalTy.Derivation A B) :
      AnnotatedHasType Φ Γ β a B

/-- Forget explicit coercion syntax back into the generic minimal-subtyping
typing judgment. -/
def AnnotatedHasType.forget : AnnotatedHasType Φ Γ β a A →
    Isotope.LambdaIter.LocallyNameless.HasType
      (τ := MinimalTy α) (ν := ν) Φ Γ β a A
  | .fv h => .fv h
  | .bv => .bv
  | .op h => .op h.forget
  | .let₁ ha hb => .let₁ ha.forget hb.forget
  | .unit => .unit
  | .pair ha hb => .pair ha.forget hb.forget
  | .let₂ ha hc => .let₂ ha.forget hc.forget
  | .inl h => .inl h.forget
  | .inr h => .inr h.forget
  | .case he hl hr => .case he.forget hl.forget hr.forget
  | .abort h => .abort h.forget
  | .iter ha hb => .iter ha.forget hb.forget
  | .sub h d => .sub h.forget d.toWitness

/-- A term together with its derivation in the no-subtyping core. -/
structure Elaborated (Φ : Type q) [HasTy Φ (MinimalTy α)]
    (Γ : Ctx ν (MinimalTy α)) (β : BoundCtx (MinimalTy α) n)
    (A : MinimalTy α) where
  term : Tm ν Φ n
  hasType : HasType Φ Γ β term A

/-- Elaborate a fully annotated minimal-subtyping typing derivation by
inserting only ordinary lambda-iter constructs. -/
def AnnotatedHasType.elaborate : AnnotatedHasType Φ Γ β a A →
    Elaborated (α := α) (ν := ν) Φ Γ β A
  | .fv h => ⟨.fv _, .fv h⟩
  | .bv => ⟨.bv _, .bv⟩
  | .op h =>
      let e := h.elaborate
      ⟨.op _ e.term, .op e.hasType⟩
  | .let₁ ha hb =>
      let ea := ha.elaborate
      let eb := hb.elaborate
      ⟨.let₁ ea.term eb.term, .let₁ ea.hasType eb.hasType⟩
  | .unit => ⟨.unit, .unit⟩
  | .pair ha hb =>
      let ea := ha.elaborate
      let eb := hb.elaborate
      ⟨.pair ea.term eb.term, .pair ea.hasType eb.hasType⟩
  | .let₂ ha hc =>
      let ea := ha.elaborate
      let ec := hc.elaborate
      ⟨.let₂ ea.term ec.term, .let₂ ea.hasType ec.hasType⟩
  | .inl h =>
      let e := h.elaborate
      ⟨.inl e.term, .inl e.hasType⟩
  | .inr h =>
      let e := h.elaborate
      ⟨.inr e.term, .inr e.hasType⟩
  | .case he hl hr =>
      let ee := he.elaborate
      let el := hl.elaborate
      let er := hr.elaborate
      ⟨.case ee.term el.term er.term, .case ee.hasType el.hasType er.hasType⟩
  | .abort h =>
      let e := h.elaborate
      ⟨.abort e.term, .abort e.hasType⟩
  | .iter ha hb =>
      let ea := ha.elaborate
      let eb := hb.elaborate
      ⟨.iter ea.term eb.term, .iter ea.hasType eb.hasType⟩
  | .sub h d =>
      let e := h.elaborate
      ⟨coeTm d e.term, coeTm_hasType d e.hasType⟩

section TruncationObstruction

variable (α)

/-- There are two explicit coercions from empty to unit: initial elimination
and evaluation followed by discard. -/
def emptyUnitByAbort : MinimalTy.Derivation
    (LambdaIter.empty : MinimalTy α) LambdaIter.unit :=
  MinimalTy.Derivation.empty LambdaIter.unit

def emptyUnitByDiscard : MinimalTy.Derivation
    (LambdaIter.empty : MinimalTy α) LambdaIter.unit :=
  MinimalTy.Derivation.unit LambdaIter.empty

/-- Their erased minimal-subtyping witnesses coincide, as all witnesses do. -/
theorem emptyUnit_erasure_eq :
    (emptyUnitByAbort α).toWitness =
      (emptyUnitByDiscard α).toWitness :=
  MinimalTy.subty_unique _ _

/-- But the induced raw terms are distinct.  Consequently `coeTm` cannot
factor through the propositionally truncated `MinimalTy.Witness` while
preserving both explicit choices. -/
theorem emptyUnit_coeTm_ne :
    coeTm (ν := ν) (Φ := Φ) (emptyUnitByAbort α)
        (.bv (0 : Fin 1)) ≠
      coeTm (ν := ν) (Φ := Φ) (emptyUnitByDiscard α)
        (.bv (0 : Fin 1)) := by
  intro h
  cases h

end TruncationObstruction

end NoSubtyping.LocallyNameless

end Isotope.LambdaIter
