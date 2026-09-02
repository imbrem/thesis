import Isotope.LambdaSSA.Translation.ANF
import Isotope.LambdaIter.Metatheory

/-! # Administrative elaboration into A-normal form -/

namespace Isotope.LambdaSSA.Translation.ANF.Elaboration

open Isotope.LambdaIter
open Isotope.LambdaIter.LocallyNameless

private def up (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

def atomRename (ρ : Fin n → Fin m) : Atom ν Φ n → Atom ν Φ m
  | .fv x => .fv x
  | .bv i => .bv (ρ i)
  | .op f a => .op f (atomRename ρ a)
  | .unit => .unit
  | .pair a b => .pair (atomRename ρ a) (atomRename ρ b)
  | .inl a => .inl (atomRename ρ a)
  | .inr a => .inr (atomRename ρ a)
  | .abort a => .abort (atomRename ρ a)

mutual
  def programRename (ρ : Fin n → Fin m) : Program ν Φ n → Program ν Φ m
    | .ret a => .ret (atomRename ρ a)
    | .let₁ i b => .let₁ (instrRename ρ i) (programRename (up ρ) b)
    | .let₂ a b => .let₂ (atomRename ρ a) (programRename (up (up ρ)) b)

  def instrRename (ρ : Fin n → Fin m) : Instr ν Φ n → Instr ν Φ m
    | .atom a => .atom (atomRename ρ a)
    | .case e l r => .case (atomRename ρ e)
        (programRename (up ρ) l) (programRename (up ρ) r)
    | .iter a b => .iter (atomRename ρ a) (programRename (up ρ) b)
end

private def underBinder : Fin (n + 1) → Fin (n + 2) :=
  Fin.cases 0 (fun i => Fin.succ (Fin.succ i))

private def underTwoBinders : Fin (n + 1) → Fin (n + 3) :=
  Fin.cases 0 (fun i => Fin.succ (Fin.succ (Fin.succ i)))

/-- Sequence an ANF program and bind its returned value for a continuation. -/
def bind : Program ν Φ n → Program ν Φ (n + 1) → Program ν Φ n
  | .ret a, k => .let₁ (.atom a) k
  | .let₁ i b, k => .let₁ i (bind b (programRename underBinder k))
  | .let₂ a b, k => .let₂ a (bind b (programRename underTwoBinders k))

/-- Administrative normalization of every exact lambda-iter constructor. -/
def elaborate : {n : Nat} → Tm ν Φ n → Program ν Φ n
  | _, .fv x => .ret (.fv x)
  | _, .bv i => .ret (.bv i)
  | _, .op f a => bind (elaborate a) (.ret (.op f (.bv 0)))
  | _, .let₁ a b => bind (elaborate a) (elaborate b)
  | _, .unit => .ret .unit
  | _, .pair a b =>
      bind (elaborate a) (bind (programRename Fin.succ (elaborate b))
        (.ret (.pair (.bv 1) (.bv 0))))
  | _, .let₂ a b =>
      bind (elaborate a) (.let₂ (.bv 0) (programRename
        (Fin.cases 0 (Fin.cases 1 (fun i => Fin.succ (Fin.succ (Fin.succ i)))))
        (elaborate b)))
  | _, .inl a => bind (elaborate a) (.ret (.inl (.bv 0)))
  | _, .inr a => bind (elaborate a) (.ret (.inr (.bv 0)))
  | _, .case e l r =>
      bind (elaborate e) (.let₁ (.case (.bv 0)
        (programRename underBinder (elaborate l))
        (programRename underBinder (elaborate r)))
        (.ret (.bv 0)))
  | _, .abort a => bind (elaborate a) (.ret (.abort (.bv 0)))
  | _, .iter a b =>
      bind (elaborate a) (.let₁ (.iter (.bv 0)
        (programRename underBinder (elaborate b)))
        (.ret (.bv 0)))

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

def atomRename_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {a : Atom ν Φ n} {A : τ}
    (ρ : TypedRenaming β β') : Atom.HasType Γ β a A →
    Atom.HasType Γ β' (atomRename ρ.toFun a) A
  | .fv h => .fv h
  | .bv => ρ.typed _ ▸ .bv
  | .op h => .op (atomRename_hasType ρ h)
  | .unit => .unit
  | .pair ha hb => .pair (atomRename_hasType ρ ha) (atomRename_hasType ρ hb)
  | .inl h => .inl (atomRename_hasType ρ h)
  | .inr h => .inr (atomRename_hasType ρ h)
  | .abort h => .abort (atomRename_hasType ρ h)

mutual
  def programRename_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n} {β' : BoundCtx τ m}
      {p : Program ν Φ n} {A : τ}
      (ρ : TypedRenaming β β') : Program.HasType Γ β p A →
      Program.HasType Γ β' (programRename ρ.toFun p) A
    | .ret h => .ret (atomRename_hasType ρ h)
    | .let₁ hi hb => .let₁ (instrRename_hasType ρ hi)
        (programRename_hasType (ρ.up _) hb)
    | .let₂ ha hb => .let₂ (atomRename_hasType ρ ha)
        (programRename_hasType ((ρ.up _).up _) hb)

  def instrRename_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n} {β' : BoundCtx τ m}
      {i : Instr ν Φ n} {A : τ}
      (ρ : TypedRenaming β β') : Instr.HasType Γ β i A →
      Instr.HasType Γ β' (instrRename ρ.toFun i) A
    | .atom h => .atom (atomRename_hasType ρ h)
    | .case he hl hr => .case (atomRename_hasType ρ he)
        (programRename_hasType (ρ.up _) hl) (programRename_hasType (ρ.up _) hr)
    | .iter ha hb => .iter (atomRename_hasType ρ ha)
        (programRename_hasType (ρ.up _) hb)
end

private def insertTwoUnderBinder (β : BoundCtx τ n) (X Y A : τ) :
    TypedRenaming (.snoc β A) (.snoc (.snoc (.snoc β X) Y) A) where
  toFun := underTwoBinders
  typed := Fin.cases rfl (fun _ => rfl)

def bind_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {p : Program ν Φ n} {A B : τ} {k : Program ν Φ (n + 1)} :
    Program.HasType Γ β p A →
    Program.HasType Γ (.snoc β A) k B → Program.HasType Γ β (bind p k) B
  | .ret ha, hk => .let₁ (.atom ha) hk
  | .let₁ (A := X) hi hb, hk => .let₁ hi
      (bind_hasType hb (programRename_hasType
        (TypedRenaming.underBinder β X A) hk))
  | .let₂ (A := X) (B := Y) ha hb, hk => .let₂ ha
      (bind_hasType hb (programRename_hasType
        (insertTwoUnderBinder β X Y A) hk))

/-- Exact typing preservation for administrative elaboration. -/
def elaborate_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} :
    HasType Φ Γ β t A → Program.HasType Γ β (elaborate t) A
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
          (TypedRenaming.underTwoBinders β (LambdaIter.tensor X Y) X Y)
          (elaborate_hasType hb)))
  | .inl ha => bind_hasType (elaborate_hasType ha) (.ret (.inl .bv))
  | .inr hb => bind_hasType (elaborate_hasType hb) (.ret (.inr .bv))
  | .case (A := X) (B := Y) he hl hr =>
      bind_hasType (elaborate_hasType he) (.let₁
        (.case .bv
          (programRename_hasType (TypedRenaming.underBinder β (LambdaIter.coprod X Y) X)
            (elaborate_hasType hl))
          (programRename_hasType (TypedRenaming.underBinder β (LambdaIter.coprod X Y) Y)
            (elaborate_hasType hr)))
        (.ret .bv))
  | .abort ha => bind_hasType (elaborate_hasType ha) (.ret (.abort .bv))
  | .iter (A := X) ha hb =>
      bind_hasType (elaborate_hasType ha) (.let₁
        (.iter .bv (programRename_hasType
          (TypedRenaming.underBinder β X X) (elaborate_hasType hb)))
        (.ret .bv))

/-- Forgetting the elaborated ANF program yields an exactly typed
lambda-iter term with the original source and target contexts. -/
def elaborate_forget_hasType {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :
    HasType Φ Γ β (elaborate t).toTm A :=
  (elaborate_hasType h).toLambdaIter

end Isotope.LambdaSSA.Translation.ANF.Elaboration
