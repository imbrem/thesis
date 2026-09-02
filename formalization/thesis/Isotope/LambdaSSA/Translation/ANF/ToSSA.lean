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

mutual
  inductive SimpleInstr : Instr Empty Φ n → Type _ where
    | atom (a : Atom Empty Φ n) : SimpleInstr (.atom a)
    | case (e : Atom Empty Φ n) : SimpleProgram left → SimpleProgram right →
        SimpleInstr (.case e left right)

  inductive SimpleProgram : Program Empty Φ n → Type _ where
    | ret (a : Atom Empty Φ n) : SimpleProgram (.ret a)
    | let₁ : SimpleInstr i → SimpleProgram body → SimpleProgram (.let₁ i body)
    | let₂ : SimpleProgram body → SimpleProgram (.let₂ a body)
end

/-- Compile a straight-line ANF program in CPS, branching to `result` with
its returned value. -/
def simpleProgram (result : Nat) : {p : Program Empty Φ n} →
    SimpleProgram p → LambdaSSA.Region Φ
  | _, .ret a => .br result (atom a)
  | _, .let₁ (.atom a) hb => .let₁ (atom a) (simpleProgram result hb)
  | _, .let₁ (.case e hl hr) hb =>
      .cfg (.case (atom e) (simpleProgram 0 hl) (simpleProgram 0 hr)) 1
        (fun _ => simpleProgram (result + 1) hb)
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

theorem at_succ {L : LambdaSSA.LCtx τ} (h : LambdaSSA.At L result A) :
    LambdaSSA.At (X :: L) (result + 1) A := by
  simpa [LambdaSSA.At] using h

def simpleProgram_hasType {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {p : Program Empty Φ n} (hs : SimpleProgram p)
    (h : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β p A)
    (hout : LambdaSSA.At L result A) :
    LambdaSSA.Region.HasType (LocallyNameless.ToDeBruijn.context β)
      (simpleProgram result hs) L := by
  cases hs with
  | ret a =>
      cases h with
      | ret ha => exact .br hout (atom_hasType ha)
  | let₁ hi hb =>
      cases h with
      | let₁ hInstr hBody =>
          cases hi with
          | atom a =>
              cases hInstr with
              | atom ha =>
                  exact LambdaSSA.Region.HasType.let₁ (atom_hasType ha)
                    (simpleProgram_hasType hb hBody hout)
          | case e hl hr =>
              cases hInstr with
              | case he hleft hright =>
                  refine LambdaSSA.Region.HasType.cfg (fun _ : Fin 1 => _) ?_
                    (fun _ => simpleProgram_hasType hb hBody (at_succ hout))
                  exact LambdaSSA.Region.HasType.case (atom_hasType he)
                      (simpleProgram_hasType hl hleft (result := 0) (by simp [LambdaSSA.At]))
                      (simpleProgram_hasType hr hright (result := 0) (by simp [LambdaSSA.At]))
  | let₂ hb =>
      cases h with
      | let₂ ha hBody =>
          exact LambdaSSA.Region.HasType.let₂ (atom_hasType ha)
            (simpleProgram_hasType hb hBody hout)
termination_by sizeOf p

end Isotope.LambdaSSA.Translation.ANF.ToSSA
