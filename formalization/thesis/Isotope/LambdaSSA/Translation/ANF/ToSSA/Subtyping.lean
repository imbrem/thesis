import Isotope.LambdaSSA.Translation.ANF.Elaboration.Subtyping
import Isotope.LambdaSSA.Translation.ANF.ToSSA
import Isotope.LambdaSSA.Subtyping.Structural

/-! # Proof-relevant ANF-to-SSA typing preservation -/

namespace Isotope.LambdaSSA.Translation.ANF.ToSSA.Subtyping

open Isotope.LambdaIter
open Isotope.LambdaSSA.Translation.ANF

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
variable {Φ : Type q} [HasTy Φ τ]

def atom_hasType {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : ANF.Atom Empty Φ n} {A : τ} :
    ANF.Subtyping.Atom.HasType (Ctx.nil : Ctx Empty τ) β a A →
    LambdaSSA.Subtyping.Tm.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) (ToSSA.atom a) A
  | .fv h => nomatch h
  | .bv => .var (LambdaSSA.LocallyNameless.ToDeBruijn.getElem_context _ _)
  | .op h => .op (atom_hasType h)
  | .unit => .unit
  | .pair ha hb => .pair (atom_hasType ha) (atom_hasType hb)
  | .inl h => .inl (atom_hasType h)
  | .inr h => .inr (atom_hasType h)
  | .abort h => .abort (atom_hasType h)
  | .sub h hAB => .sub (atom_hasType h) hAB

def simpleProgram_hasType {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {p : ANF.Program Empty Φ n} (hs : ToSSA.SimpleProgram p)
    {A C : τ}
    (h : ANF.Subtyping.Program.HasType (Ctx.nil : Ctx Empty τ) β p A)
    (hAC : Subty A C) {L : LambdaSSA.LCtx τ} {result : Nat}
    (hout : LambdaSSA.At L result C) :
    LambdaSSA.Subtyping.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β)
      (ToSSA.simpleProgram result hs) L := by
  cases hs with
  | ret a =>
      cases h with
      | ret ha => exact .br hout (.sub (atom_hasType ha) hAC)
  | let₁ hi sb =>
      cases h with
      | let₁ hInstr hBody =>
        rename_i Z
        cases hi with
        | atom a =>
            cases hInstr with
            | atom ha =>
                exact .let₁ (atom_hasType ha)
                  (simpleProgram_hasType sb hBody hAC hout)
        | case e sl sr =>
            cases hInstr with
            | case he hl hr =>
                refine .cfg (fun _ : Fin 1 => Z) ?_ ?_
                · exact .case (atom_hasType he)
                    (simpleProgram_hasType sl hl (Subty.refl _)
                      (by simp [LambdaSSA.At]))
                    (simpleProgram_hasType sr hr (Subty.refl _)
                      (by simp [LambdaSSA.At]))
                · intro i
                  exact simpleProgram_hasType sb hBody hAC (ToSSA.at_succ hout)
        | iter init loop =>
            cases hInstr with
            | iter hinit hloop =>
                rename_i X
                refine .cfg (ToSSA.twoLabels X (coprod Z X)) ?_ ?_
                · exact .br (by simp [LambdaSSA.At, ToSSA.twoLabels])
                    (atom_hasType hinit)
                · intro i
                  refine Fin.cases ?_ (fun j => ?_) i
                  · simpa [ToSSA.twoLabels] using
                      simpleProgram_hasType loop hloop (Subty.refl _)
                        (result := 1) (by simp [LambdaSSA.At])
                  · have hj : j = 0 := Subsingleton.elim _ _
                    subst j
                    simp only [ToSSA.twoLabels]
                    apply LambdaSSA.Subtyping.Region.HasType.case (A := Z) (B := X)
                      (LambdaSSA.Subtyping.Tm.HasType.var
                        (Γ := coprod Z X ::
                          LambdaSSA.LocallyNameless.ToDeBruijn.context β)
                        (A := coprod Z X) (i := 0)
                        (by simp [LambdaSSA.At]))
                    · exact LambdaSSA.Subtyping.Region.HasType.renameVars
                        ((LambdaSSA.Ren.wk
                          (LambdaSSA.LocallyNameless.ToDeBruijn.context β)
                          (coprod Z X)).lift Z)
                        (simpleProgram_hasType sb hBody hAC
                          (result := result + 2)
                          (by simpa [LambdaSSA.At, Fin.cases] using hout))
                    · exact LambdaSSA.Subtyping.Region.HasType.br (A := X) (ℓ := 0)
                        (by simp [LambdaSSA.At, ToSSA.twoLabels])
                        (LambdaSSA.Subtyping.Tm.HasType.var
                          (Γ := X :: coprod Z X ::
                            LambdaSSA.LocallyNameless.ToDeBruijn.context β)
                          (A := X) (i := 0) (by simp [LambdaSSA.At]))
  | let₂ sb =>
      cases h with
      | let₂ ha hBody =>
          exact .let₂ (atom_hasType ha)
            (simpleProgram_hasType sb hBody hAC hout)
termination_by sizeOf p

def program_hasType {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {p : ANF.Program Empty Φ n} {A : τ}
    (h : ANF.Subtyping.Program.HasType (Ctx.nil : Ctx Empty τ) β p A)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A) :
    LambdaSSA.Subtyping.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β)
      (ToSSA.program result p) L :=
  simpleProgram_hasType (ToSSA.simpleProgram_all p) h (Subty.refl A) hout

end Isotope.LambdaSSA.Translation.ANF.ToSSA.Subtyping
