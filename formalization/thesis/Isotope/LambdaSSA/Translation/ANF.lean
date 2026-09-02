import Isotope.LambdaIter.Typing

/-!
# A-normal forms for exact lambda-iter

This is the intermediate language used by the expression-to-SSA construction:
atoms contain no binders or control, instructions may contain structured case
or iteration, and programs are sequences of one- or two-result bindings.
-/

namespace Isotope.LambdaSSA.Translation.ANF

open Isotope.LambdaIter

universe u v w q

/-- Binder-free values and primitive computations. -/
inductive Atom (ν : Type w) (Φ : Type q) (n : Nat) where
  | fv (x : ν)
  | bv (i : Fin n)
  | op (f : Φ) (a : Atom ν Φ n)
  | unit
  | pair (a b : Atom ν Φ n)
  | inl (a : Atom ν Φ n)
  | inr (a : Atom ν Φ n)
  | abort (a : Atom ν Φ n)

mutual
  /-- ANF programs and the instructions bound by their `let₁` nodes. -/
  inductive Program (ν : Type w) (Φ : Type q) : Nat → Type (max w q) where
    | ret (a : Atom ν Φ n) : Program ν Φ n
    | let₁ (i : Instr ν Φ n) (body : Program ν Φ (n + 1)) : Program ν Φ n
    | let₂ (a : Atom ν Φ n) (body : Program ν Φ (n + 2)) : Program ν Φ n

  inductive Instr (ν : Type w) (Φ : Type q) : Nat → Type (max w q) where
    | atom (a : Atom ν Φ n) : Instr ν Φ n
    | case (e : Atom ν Φ n) (left right : Program ν Φ (n + 1)) : Instr ν Φ n
    | iter (init : Atom ν Φ n) (body : Program ν Φ (n + 1)) : Instr ν Φ n
end

/-- Forget the ANF restriction. -/
def Atom.toTm : Atom ν Φ n → Isotope.LambdaIter.LocallyNameless.Tm ν Φ n
  | .fv x => .fv x
  | .bv i => .bv i
  | .op f a => .op f a.toTm
  | .unit => .unit
  | .pair a b => .pair a.toTm b.toTm
  | .inl a => .inl a.toTm
  | .inr a => .inr a.toTm
  | .abort a => .abort a.toTm

mutual
  /-- Forget an ANF program to its exact lambda-iter term. -/
  def Program.toTm : Program ν Φ n → Isotope.LambdaIter.LocallyNameless.Tm ν Φ n
    | .ret a => a.toTm
    | .let₁ i body => .let₁ i.toTm body.toTm
    | .let₂ a body => .let₂ a.toTm body.toTm

  /-- Forget an ANF instruction to its exact lambda-iter term. -/
  def Instr.toTm : Instr ν Φ n → Isotope.LambdaIter.LocallyNameless.Tm ν Φ n
    | .atom a => a.toTm
    | .case e left right => .case e.toTm left.toTm right.toTm
    | .iter init body => .iter init.toTm body.toTm
end

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

/-- Exact typing of ANF atoms. -/
inductive Atom.HasType (Γ : Ctx ν τ) (β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n) :
    Atom ν Φ n → τ → Type (max u w q) where
  | fv (h : Γ.lookup x = some A) : HasType Γ β (.fv x) A
  | bv : HasType Γ β (.bv i) (β.get i)
  | op (ha : HasType Γ β a (instrSrc f)) : HasType Γ β (.op f a) (instrTrg f)
  | unit : HasType Γ β .unit LambdaIter.unit
  | pair (ha : HasType Γ β a A) (hb : HasType Γ β b B) :
      HasType Γ β (.pair a b) (LambdaIter.tensor A B)
  | inl (ha : HasType Γ β a A) : HasType Γ β (.inl a) (LambdaIter.coprod A B)
  | inr (hb : HasType Γ β b B) : HasType Γ β (.inr b) (LambdaIter.coprod A B)
  | abort (ha : HasType Γ β a LambdaIter.empty) : HasType Γ β (.abort a) A

mutual
  /-- Exact typing of ANF programs. -/
  inductive Program.HasType (Γ : Ctx ν τ) :
      {n : Nat} → Isotope.LambdaIter.LocallyNameless.BoundCtx τ n → Program ν Φ n → τ → Type (max u w q) where
    | ret {n : Nat} {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
        {a : Atom ν Φ n}
        (ha : Atom.HasType Γ β a A) : Program.HasType Γ β (.ret a) A
    | let₁ {n : Nat} {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
        {i : Instr ν Φ n}
        (hi : Instr.HasType Γ β i A)
        {body : Program ν Φ (n + 1)}
        (hb : Program.HasType Γ (.snoc β A) body B) :
        Program.HasType Γ β (Program.let₁ (n := n) i body) B
    | let₂ {n : Nat} {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
        {a : Atom ν Φ n}
        (ha : Atom.HasType Γ β a (LambdaIter.tensor A B))
        {body : Program ν Φ (n + 2)}
        (hc : Program.HasType Γ (.snoc (.snoc β A) B) body C) :
        Program.HasType Γ β (Program.let₂ (n := n) a body) C

  /-- Exact typing of ANF instructions. -/
  inductive Instr.HasType (Γ : Ctx ν τ) :
      {n : Nat} → Isotope.LambdaIter.LocallyNameless.BoundCtx τ n → Instr ν Φ n → τ → Type (max u w q) where
    | atom {n : Nat} {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
        {a : Atom ν Φ n}
        (ha : Atom.HasType Γ β a A) : Instr.HasType Γ β (.atom a) A
    | case {n : Nat} {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
        {e : Atom ν Φ n}
        (he : Atom.HasType Γ β e (LambdaIter.coprod A B))
        {left right : Program ν Φ (n + 1)}
        (hl : Program.HasType Γ (.snoc β A) left C)
        (hr : Program.HasType Γ (.snoc β B) right C) :
        Instr.HasType Γ β (Instr.case (n := n) e left right) C
    | iter {n : Nat} {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
        {init : Atom ν Φ n} (ha : Atom.HasType Γ β init A)
        {body : Program ν Φ (n + 1)}
        (hb : Program.HasType Γ (.snoc β A) body (LambdaIter.coprod B A)) :
        Instr.HasType Γ β (Instr.iter (n := n) init body) B
end

/-- Atom typing is preserved by forgetting ANF structure. -/
def Atom.HasType.toLambdaIter {Γ : Ctx ν τ} {n : Nat}
    {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : Atom ν Φ n} {A : τ} : Atom.HasType Γ β a A →
    Isotope.LambdaIter.LocallyNameless.HasType Φ Γ β a.toTm A
  | .fv h => .fv h
  | .bv => .bv
  | .op h => .op h.toLambdaIter
  | .unit => .unit
  | .pair ha hb => .pair ha.toLambdaIter hb.toLambdaIter
  | .inl h => .inl h.toLambdaIter
  | .inr h => .inr h.toLambdaIter
  | .abort h => .abort h.toLambdaIter

mutual
  /-- Program typing is preserved by forgetting ANF structure. -/
  def Program.HasType.toLambdaIter {Γ : Ctx ν τ} {n : Nat}
      {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
      {p : Program ν Φ n} {A : τ} : Program.HasType Γ β p A →
      Isotope.LambdaIter.LocallyNameless.HasType Φ Γ β p.toTm A
    | .ret h => h.toLambdaIter
    | .let₁ hi hb => .let₁ hi.toLambdaIter hb.toLambdaIter
    | .let₂ ha hc => .let₂ ha.toLambdaIter hc.toLambdaIter

  /-- Instruction typing is preserved by forgetting ANF structure. -/
  def Instr.HasType.toLambdaIter {Γ : Ctx ν τ} {n : Nat}
      {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
      {i : Instr ν Φ n} {A : τ} : Instr.HasType Γ β i A →
      Isotope.LambdaIter.LocallyNameless.HasType Φ Γ β i.toTm A
    | .atom h => h.toLambdaIter
    | .case he hl hr => .case he.toLambdaIter hl.toLambdaIter hr.toLambdaIter
    | .iter ha hb => .iter ha.toLambdaIter hb.toLambdaIter
end

end Isotope.LambdaSSA.Translation.ANF
