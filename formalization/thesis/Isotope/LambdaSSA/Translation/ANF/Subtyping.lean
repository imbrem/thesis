import Isotope.LambdaSSA.Translation.ANF
import Isotope.LambdaIter.Subtyping.LocallyNameless.Typing

/-! # Proof-relevant subtyping for administrative normal form

The raw ANF syntax is unchanged.  Subtype witnesses live only in typing
derivations, in parallel with the exact ANF judgment.
-/

namespace Isotope.LambdaSSA.Translation.ANF.Subtyping

open Isotope.LambdaIter

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

inductive Atom.HasType (Γ : Ctx ν τ)
    (β : LambdaIter.LocallyNameless.BoundCtx τ n) :
    ANF.Atom ν Φ n → τ → Type (max u w q) where
  | fv (h : Γ.lookup x = some A) : HasType Γ β (.fv x) A
  | bv : HasType Γ β (.bv i) (β.get i)
  | op (ha : HasType Γ β a (instrSrc f)) : HasType Γ β (.op f a) (instrTrg f)
  | unit : HasType Γ β .unit LambdaIter.unit
  | pair (ha : HasType Γ β a A) (hb : HasType Γ β b B) :
      HasType Γ β (.pair a b) (tensor A B)
  | inl (ha : HasType Γ β a A) : HasType Γ β (.inl a) (coprod A B)
  | inr (hb : HasType Γ β b B) : HasType Γ β (.inr b) (coprod A B)
  | abort (ha : HasType Γ β a empty) : HasType Γ β (.abort a) A
  | sub (ha : HasType Γ β a A) (hAB : Subty A B) : HasType Γ β a B

mutual
  inductive Program.HasType (Γ : Ctx ν τ) :
      {n : Nat} → LambdaIter.LocallyNameless.BoundCtx τ n →
      ANF.Program ν Φ n → τ → Type (max u w q) where
    | ret {n} {β : LambdaIter.LocallyNameless.BoundCtx τ n}
        {a : ANF.Atom ν Φ n} (ha : Atom.HasType Γ β a A) :
        Program.HasType Γ β (.ret a) A
    | let₁ {n} {β : LambdaIter.LocallyNameless.BoundCtx τ n}
        {i : ANF.Instr ν Φ n} (hi : Instr.HasType Γ β i A)
        {body : ANF.Program ν Φ (n + 1)}
        (hb : Program.HasType Γ (.snoc β A) body B) :
        Program.HasType Γ β (.let₁ i body) B
    | let₂ {n} {β : LambdaIter.LocallyNameless.BoundCtx τ n}
        {a : ANF.Atom ν Φ n} (ha : Atom.HasType Γ β a (tensor A B))
        {body : ANF.Program ν Φ (n + 2)}
        (hc : Program.HasType Γ (.snoc (.snoc β A) B) body C) :
        Program.HasType Γ β (.let₂ a body) C

  inductive Instr.HasType (Γ : Ctx ν τ) :
      {n : Nat} → LambdaIter.LocallyNameless.BoundCtx τ n →
      ANF.Instr ν Φ n → τ → Type (max u w q) where
    | atom {n} {β : LambdaIter.LocallyNameless.BoundCtx τ n}
        {a : ANF.Atom ν Φ n} (ha : Atom.HasType Γ β a A) :
        Instr.HasType Γ β (.atom a) A
    | case {n} {β : LambdaIter.LocallyNameless.BoundCtx τ n}
        {e : ANF.Atom ν Φ n} (he : Atom.HasType Γ β e (coprod A B))
        {left right : ANF.Program ν Φ (n + 1)}
        (hl : Program.HasType Γ (.snoc β A) left C)
        (hr : Program.HasType Γ (.snoc β B) right C) :
        Instr.HasType Γ β (.case e left right) C
    | iter {n} {β : LambdaIter.LocallyNameless.BoundCtx τ n}
        {init : ANF.Atom ν Φ n} (ha : Atom.HasType Γ β init A)
        {body : ANF.Program ν Φ (n + 1)}
        (hb : Program.HasType Γ (.snoc β A) body (coprod B A)) :
        Instr.HasType Γ β (.iter init body) B
end

def Atom.HasType.toLambdaIter {Γ : Ctx ν τ} {n : Nat}
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : ANF.Atom ν Φ n} {A : τ} : Atom.HasType Γ β a A →
    LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β a.toTm A
  | .fv h => .fv h
  | .bv => .bv
  | .op h => .op h.toLambdaIter
  | .unit => .unit
  | .pair ha hb => .pair ha.toLambdaIter hb.toLambdaIter
  | .inl h => .inl h.toLambdaIter
  | .inr h => .inr h.toLambdaIter
  | .abort h => .abort h.toLambdaIter
  | .sub h hAB => .sub h.toLambdaIter hAB

mutual
  def Program.HasType.toLambdaIter {Γ : Ctx ν τ} {n : Nat}
      {β : LambdaIter.LocallyNameless.BoundCtx τ n}
      {p : ANF.Program ν Φ n} {A : τ} : Program.HasType Γ β p A →
      LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β p.toTm A
    | .ret h => h.toLambdaIter
    | .let₁ hi hb => .let₁ hi.toLambdaIter hb.toLambdaIter
    | .let₂ ha hb => .let₂ ha.toLambdaIter hb.toLambdaIter

  def Instr.HasType.toLambdaIter {Γ : Ctx ν τ} {n : Nat}
      {β : LambdaIter.LocallyNameless.BoundCtx τ n}
      {i : ANF.Instr ν Φ n} {A : τ} : Instr.HasType Γ β i A →
      LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β i.toTm A
    | .atom h => h.toLambdaIter
    | .case he hl hr => .case he.toLambdaIter hl.toLambdaIter hr.toLambdaIter
    | .iter ha hb => .iter ha.toLambdaIter hb.toLambdaIter
end

end Isotope.LambdaSSA.Translation.ANF.Subtyping
