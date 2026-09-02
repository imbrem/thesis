import Isotope.LambdaSSA.Translation.ANF
import Isotope.LambdaSSA.LocallyNameless.ToDeBruijn.Typing

/-! # CPS compilation of typed ANF to lambda-SSA -/

namespace Isotope.LambdaSSA.Translation.ANF.ToSSA

open Isotope.LambdaIter

def atom : Atom Empty Φ n → LambdaSSA.Tm Φ
  | .fv x => Empty.elim x
  | .bv i => .var i
  | .op f a => .op f (atom a)
  | .unit => .unit
  | .pair a b => .pair (atom a) (atom b)
  | .inl a => .inl (atom a)
  | .inr a => .inr (atom a)
  | .abort a => .abort (atom a)

/-- The straight-line fragment, before compiling control instructions to CFGs. -/
inductive Instr.Simple : Instr Empty Φ n → Type _ where
  | atom (a : Atom Empty Φ n) : Simple (.atom a)

inductive Program.Simple : Program Empty Φ n → Type _ where
  | ret (a : Atom Empty Φ n) : Simple (.ret a)
  | let₁ : Instr.Simple i → Program.Simple body → Simple (.let₁ i body)
  | let₂ : Program.Simple body → Simple (.let₂ a body)

def simpleInstr : {i : Instr Empty Φ n} → Instr.Simple i → LambdaSSA.Tm Φ
  | _, .atom a => atom a

/-- Compile a straight-line ANF program in CPS, branching to `result` with
its returned value. -/
def simpleProgram (result : Nat) : {p : Program Empty Φ n} →
    Program.Simple p → LambdaSSA.Region Φ
  | _, .ret a => .br result (atom a)
  | _, .let₁ hi hb => .let₁ (simpleInstr hi) (simpleProgram result hb)
  | _, .let₂ (a := a) hb => .let₂ (atom a) (simpleProgram result hb)

variable {τ : Type u} [TypeFormers τ]
variable {Φ : Type q} [HasTy Φ τ]

def atom_hasType {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : Atom Empty Φ n} (h : Atom.HasType
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β a A) :
    LambdaSSA.Tm.HasType (LocallyNameless.ToDeBruijn.context β) (atom a) A := by
  induction h with
  | fv h => cases h
  | bv => exact .var (LocallyNameless.ToDeBruijn.getElem_context _ _)
  | op _ ih => exact .op ih
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | abort _ ih => exact .abort ih

def simpleInstr_hasType {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {i : Instr Empty Φ n} (hs : Instr.Simple i)
    (h : Instr.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β i A) :
    LambdaSSA.Tm.HasType (LocallyNameless.ToDeBruijn.context β)
      (simpleInstr hs) A := by
  cases hs with
  | atom _ => cases h with | atom h => exact atom_hasType h

def simpleProgram_hasType {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {p : Program Empty Φ n} (hs : Program.Simple p)
    (h : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β p A)
    (hout : LambdaSSA.At L result A) :
    LambdaSSA.Region.HasType (LocallyNameless.ToDeBruijn.context β)
      (simpleProgram result hs) L := by
  induction hs with
  | ret a =>
      cases h with
      | ret ha => exact .br hout (atom_hasType ha)
  | let₁ hi hb ih =>
      cases h with
      | let₁ hInstr hBody =>
          exact .let₁ (simpleInstr_hasType hi hInstr) (ih hBody)
  | let₂ hb ih =>
      cases h with
      | let₂ ha hBody => exact .let₂ (atom_hasType ha) (ih hBody)

end Isotope.LambdaSSA.Translation.ANF.ToSSA
