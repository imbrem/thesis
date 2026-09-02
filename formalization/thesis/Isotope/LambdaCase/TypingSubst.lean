import Isotope.LambdaCase.Typing
import Isotope.LambdaIter.Metatheory

/-! # Proof-relevant renaming and substitution for lambda-case -/

namespace Isotope.LambdaCase.LocallyNameless

variable {τ : Type u} [LambdaIter.TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {Γ Γ' : Ctx ν τ}

abbrev TypedRenaming {n m : Nat} (β : BoundCtx τ n) (β' : BoundCtx τ m) :=
  LambdaIter.LocallyNameless.TypedRenaming β β'

namespace HasType

def rename {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    (r : TypedRenaming β β') :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β' (t.rename r.toFun) A
  | _, _, .fv h => .fv h
  | _, _, .bv (i := i) => r.typed i ▸ .bv
  | _, _, .op h => .op (rename r h)
  | _, _, .let₁ ha hb => .let₁ (rename r ha) (rename (r.up _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (rename r ha) (rename r hb)
  | _, _, .let₂ ha hb => .let₂ (rename r ha) (rename ((r.up _).up _) hb)
  | _, _, .inl h => .inl (rename r h)
  | _, _, .inr h => .inr (rename r h)
  | _, _, .case he hl hr =>
      .case (rename r he) (rename (r.up _) hl) (rename (r.up _) hr)
  | _, _, .abort h => .abort (rename r h)

def lift {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (h : HasType Φ Γ β t A) :
    HasType Φ Γ (.snoc β B) t.lift A :=
  rename (LambdaIter.LocallyNameless.TypedRenaming.succ β B) h

def underBinder {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 1)}
    {A X Y : τ} (h : HasType Φ Γ (.snoc β Y) t A) :
    HasType Φ Γ (.snoc (.snoc β X) Y) t.underBinder A :=
  rename (LambdaIter.LocallyNameless.TypedRenaming.underBinder β X Y) h

def underTwoBinders {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 2)}
    {A X Y Z : τ} (h : HasType Φ Γ (.snoc (.snoc β Y) Z) t A) :
    HasType Φ Γ (.snoc (.snoc (.snoc β X) Y) Z) t.underTwoBinders A :=
  rename (LambdaIter.LocallyNameless.TypedRenaming.underTwoBinders β X Y Z) h

end HasType

def TypedSubst (β : BoundCtx τ n) (β' : BoundCtx τ m)
    (σ : Fin n → Tm ν Φ m) : Type (max u q w) :=
  (i : Fin n) → HasType Φ Γ β' (σ i) (β.get i)

namespace TypedSubst

def up {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) (A : τ) :
    TypedSubst (Γ := Γ) (.snoc β A) (.snoc β' A)
      (fun i => Fin.cases (.bv (0 : Fin (m + 1))) (fun j => (σ j).lift) i) :=
  Fin.cases (.bv) (fun i => (s i).lift)

end TypedSubst

namespace HasType

def bsubst {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β' (t.bsubst σ) A
  | _, _, .fv h => .fv h
  | _, _, .bv (i := i) => s i
  | _, _, .op h => .op (bsubst s h)
  | _, _, .let₁ ha hb => .let₁ (bsubst s ha) (bsubst (s.up _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (bsubst s ha) (bsubst s hb)
  | _, _, .let₂ ha hb => .let₂ (bsubst s ha) (bsubst ((s.up _).up _) hb)
  | _, _, .inl h => .inl (bsubst s h)
  | _, _, .inr h => .inr (bsubst s h)
  | _, _, .case he hl hr => .case (bsubst s he) (bsubst (s.up _) hl) (bsubst (s.up _) hr)
  | _, _, .abort h => .abort (bsubst s h)

def instantiate {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : HasType Φ Γ (.snoc β A) b B) (ha : HasType Φ Γ β a A) :
    HasType Φ Γ β (Tm.instantiate b a) B :=
  bsubst (σ := Fin.cases a fun i => .bv i) (Fin.cases ha fun _ => .bv) hb

end HasType
end Isotope.LambdaCase.LocallyNameless
