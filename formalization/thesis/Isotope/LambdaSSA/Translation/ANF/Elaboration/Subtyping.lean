import Isotope.LambdaSSA.Translation.ANF.Subtyping
import Isotope.LambdaSSA.Translation.ANF.Elaboration

/-! # Subtyping-preserving elaboration into ANF -/

namespace Isotope.LambdaSSA.Translation.ANF.Subtyping

open Isotope.LambdaIter
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaSSA.Translation.ANF.Elaboration

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

def atomRename_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {a : ANF.Atom ν Φ n} {A : τ} (ρ : TypedRenaming β β') :
    Atom.HasType Γ β a A → Atom.HasType Γ β' (atomRename ρ.toFun a) A
  | .fv h => .fv h
  | .bv => ρ.typed _ ▸ .bv
  | .op h => .op (atomRename_hasType ρ h)
  | .unit => .unit
  | .pair ha hb => .pair (atomRename_hasType ρ ha) (atomRename_hasType ρ hb)
  | .inl h => .inl (atomRename_hasType ρ h)
  | .inr h => .inr (atomRename_hasType ρ h)
  | .abort h => .abort (atomRename_hasType ρ h)
  | .sub h hAB => .sub (atomRename_hasType ρ h) hAB

mutual
  def programRename_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n} {β' : BoundCtx τ m}
      {p : ANF.Program ν Φ n} {A : τ} (ρ : TypedRenaming β β') :
      Program.HasType Γ β p A →
      Program.HasType Γ β' (programRename ρ.toFun p) A
    | .ret h => .ret (atomRename_hasType ρ h)
    | .let₁ hi hb => .let₁ (instrRename_hasType ρ hi)
        (programRename_hasType (ρ.up _) hb)
    | .let₂ ha hb => .let₂ (atomRename_hasType ρ ha)
        (programRename_hasType ((ρ.up _).up _) hb)

  def instrRename_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n} {β' : BoundCtx τ m}
      {i : ANF.Instr ν Φ n} {A : τ} (ρ : TypedRenaming β β') :
      Instr.HasType Γ β i A → Instr.HasType Γ β' (instrRename ρ.toFun i) A
    | .atom h => .atom (atomRename_hasType ρ h)
    | .case he hl hr => .case (atomRename_hasType ρ he)
        (programRename_hasType (ρ.up _) hl) (programRename_hasType (ρ.up _) hr)
    | .iter ha hb => .iter (atomRename_hasType ρ ha)
        (programRename_hasType (ρ.up _) hb)
end

/-- Push a result coercion to the final atom, without changing raw ANF. -/
def Program.HasType.coerceResult {Γ : Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {p : ANF.Program ν Φ n} {A B : τ}
    (hAB : Subty A B) :
    Program.HasType Γ β p A → Program.HasType Γ β p B
  | .ret ha => .ret (.sub ha hAB)
  | .let₁ hi hb => .let₁ hi (hb.coerceResult hAB)
  | .let₂ ha hb => .let₂ ha (hb.coerceResult hAB)

private def insertTwoUnderBinder (β : BoundCtx τ n) (X Y A : τ) :
    TypedRenaming (.snoc β A) (.snoc (.snoc (.snoc β X) Y) A) where
  toFun := fun i => Fin.cases 0 (fun i => Fin.succ (Fin.succ (Fin.succ i))) i
  typed := Fin.cases rfl (fun _ => rfl)

def bind_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {p : ANF.Program ν Φ n} {A B : τ} {k : ANF.Program ν Φ (n + 1)} :
    Program.HasType Γ β p A → Program.HasType Γ (.snoc β A) k B →
    Program.HasType Γ β (bind p k) B
  | .ret ha, hk => .let₁ (.atom ha) hk
  | .let₁ (A := X) hi hb, hk => .let₁ hi
      (bind_hasType hb (programRename_hasType (TypedRenaming.underBinder β X A) hk))
  | .let₂ (A := X) (B := Y) ha hb, hk => .let₂ ha
      (bind_hasType hb (programRename_hasType (insertTwoUnderBinder β X Y A) hk))

def elaborate_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm ν Φ n} {A : τ} :
    LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β t A →
    Program.HasType Γ β (elaborate t) A
  | .fv h => .ret (.fv h)
  | .bv => .ret .bv
  | .op h => bind_hasType (elaborate_hasType h) (.ret (.op .bv))
  | .let₁ ha hb => bind_hasType (elaborate_hasType ha) (elaborate_hasType hb)
  | .unit => .ret .unit
  | .pair (A := X) (B := Y) ha hb =>
      bind_hasType (elaborate_hasType ha)
        (bind_hasType (programRename_hasType (TypedRenaming.succ β X)
          (elaborate_hasType hb)) (.ret (.pair .bv .bv)))
  | .let₂ (A := X) (B := Y) ha hb =>
      bind_hasType (elaborate_hasType ha) (.let₂ .bv
        (programRename_hasType
          (TypedRenaming.underTwoBinders β (tensor X Y) X Y)
          (elaborate_hasType hb)))
  | .inl ha => bind_hasType (elaborate_hasType ha) (.ret (.inl .bv))
  | .inr hb => bind_hasType (elaborate_hasType hb) (.ret (.inr .bv))
  | .case (A := X) (B := Y) he hl hr =>
      bind_hasType (elaborate_hasType he) (.let₁
        (.case .bv
          (programRename_hasType (TypedRenaming.underBinder β (coprod X Y) X)
            (elaborate_hasType hl))
          (programRename_hasType (TypedRenaming.underBinder β (coprod X Y) Y)
            (elaborate_hasType hr)))
        (.ret .bv))
  | .abort ha => bind_hasType (elaborate_hasType ha) (.ret (.abort .bv))
  | .iter (A := X) ha hb =>
      bind_hasType (elaborate_hasType ha) (.let₁
        (.iter .bv (programRename_hasType
          (TypedRenaming.underBinder β X X) (elaborate_hasType hb)))
        (.ret .bv))
  | .sub h hAB => (elaborate_hasType h).coerceResult hAB

end Isotope.LambdaSSA.Translation.ANF.Subtyping
