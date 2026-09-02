import Isotope.LambdaSeq.Metatheory
import Isotope.LambdaCase.Metatheory.Shift
import Isotope.LambdaCase.Metatheory.EquivSubst

/-!
# Typed renaming for lambda-seq

Lambda-seq had no renaming metatheory at all: no `HasType.rename`, no algebra of
`Tm.rename`, no stability of `Equiv`.  This file supplies exactly what the
one-variable syntactic category of `Isotope/LambdaSeq/Models/SynCategory.lean`
needs, and nothing more.

As elsewhere in this development, the raw-syntax lemmas are *transported* rather
than reproved: `Tm.embedCase` is injective and `@[simp]`-commutes with `rename`,
`lift`, `underBinder` and `instantiate`, so each one reduces to its lambda-case
counterpart in `Isotope/LambdaCase/Metatheory/`.

`Equiv.rename`, by contrast, must be a genuine recursion on the lambda-seq
theory: `Equiv.embedCase` maps lambda-seq equations *into* lambda-case, but
there is no converse, so nothing about lambda-seq's own `Equiv` can be read back
off it.
-/

namespace Isotope.LambdaSeq.LocallyNameless

open Isotope.LambdaIter.LocallyNameless.Syntax (upRen)

namespace Syntax

variable {ν : Type w} {Φ : Type v} {n m : Nat}

@[simp] theorem rename_fv (ρ : Fin n → Fin m) (x : ν) :
    Tm.rename ρ (.fv x : Tm ν Φ n) = .fv x := rfl

@[simp] theorem rename_bv (ρ : Fin n → Fin m) (i : Fin n) :
    Tm.rename ρ (.bv i : Tm ν Φ n) = .bv (ρ i) := rfl

@[simp] theorem rename_op (ρ : Fin n → Fin m) (f : Φ) (a : Tm ν Φ n) :
    Tm.rename ρ (.op f a) = .op f (Tm.rename ρ a) := rfl

@[simp] theorem rename_let₁ (ρ : Fin n → Fin m) (a : Tm ν Φ n)
    (b : Tm ν Φ (n + 1)) :
    Tm.rename ρ (.let₁ a b) = .let₁ (Tm.rename ρ a) (Tm.rename (upRen ρ) b) := rfl

/-- Renaming commutes with weakening by one binder. -/
@[simp] theorem rename_lift (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    Tm.rename (upRen ρ) t.lift = (Tm.rename ρ t).lift :=
  Tm.embedCase_injective (by simp)

/-- Renaming commutes with inserting a binder below the newest one. -/
@[simp] theorem rename_underBinder (ρ : Fin n → Fin m) (t : Tm ν Φ (n + 1)) :
    Tm.rename (upRen (upRen ρ)) t.underBinder =
      (Tm.rename (upRen ρ) t).underBinder :=
  Tm.embedCase_injective (by simp)

/-- Renaming commutes with opening the newest binder. -/
@[simp] theorem rename_instantiate (ρ : Fin n → Fin m) (b : Tm ν Φ (n + 1))
    (a : Tm ν Φ n) :
    Tm.rename ρ (Tm.instantiate b a) =
      Tm.instantiate (Tm.rename (upRen ρ) b) (Tm.rename ρ a) :=
  Tm.embedCase_injective (by simp)

end Syntax

namespace Tm

variable {ν : Type w} {Φ : Type v} {n : Nat}

/-- Opening the binder introduced by `underBinder` with the variable it
displaced is the identity: the de Bruijn content of `𝟙 ≫ g = g`. -/
theorem instantiate_underBinder_bv_zero (t : Tm ν Φ (n + 1)) :
    Tm.instantiate (Tm.underBinder t) (.bv 0) = t :=
  Tm.embedCase_injective (by
    simpa [Tm.embedCase] using
      LambdaCase.LocallyNameless.Tm.instantiate_underBinder_bv_zero
        (Tm.embedCase t))

/-- Shifting a `let` whose body is already shifted: the de Bruijn content of
associativity of composition in the one-variable syntactic category. -/
theorem underBinder_let₁_underBinder (b c : Tm ν Φ 1) :
    Tm.underBinder (.let₁ b (Tm.underBinder c)) =
      .let₁ (Tm.underBinder b) (Tm.underBinder (Tm.underBinder c)) :=
  Tm.embedCase_injective (by
    simpa [Tm.embedCase] using
      LambdaCase.LocallyNameless.Tm.underBinder_let₁_underBinder
        (Tm.embedCase b) (Tm.embedCase c))

end Tm

variable {τ : Type u} [LambdaIter.TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε]
variable {Γ : Ctx ν τ}

/-- An exactly typed bound renaming, shared with lambda-iter. -/
abbrev TypedRenaming {n m : Nat} (β : BoundCtx τ n) (β' : BoundCtx τ m) :=
  LambdaIter.LocallyNameless.TypedRenaming β β'

/-- Typing is preserved by every exactly typed bound renaming. -/
def HasType.rename {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    (r : TypedRenaming β β') :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β' (t.rename r.toFun) A
  | _, _, .fv h => .fv h
  | _, _, .bv (i := i) => r.typed i ▸ .bv
  | _, _, .op h => .op (HasType.rename r h)
  | _, _, .let₁ ha hb => .let₁ (HasType.rename r ha) (HasType.rename (r.up _) hb)

/-- Weakening a derivation by one fresh innermost binder. -/
def HasType.lift {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (h : HasType Φ Γ β t A) : HasType Φ Γ (.snoc β B) t.lift A :=
  HasType.rename (LambdaIter.LocallyNameless.TypedRenaming.succ β B) h

/-- Inserting a fresh binder immediately below the newest one. -/
def HasType.underBinder {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 1)}
    {A X Y : τ} (h : HasType Φ Γ (.snoc β Y) t A) :
    HasType Φ Γ (.snoc (.snoc β X) Y) t.underBinder A :=
  HasType.rename
    (LambdaIter.LocallyNameless.TypedRenaming.underBinder β X Y) h

omit [DecidableEq ν] in
/-- Purity is stable under bound renaming. -/
theorem Pure.rename {pureEff : ε} {n m : Nat} (ρ : Fin n → Fin m) :
    {a : Tm ν Φ n} → Pure pureEff a → Pure pureEff (Tm.rename ρ a)
  | _, .fv => .fv
  | _, .bv => .bv
  | _, .op hf ha => .op hf (Pure.rename ρ ha)
  | _, .let₁ ha hb => .let₁ (Pure.rename ρ ha) (Pure.rename _ hb)

omit [LambdaIter.TypeFormers τ] in
/-- **The lambda-seq equational theory is stable under every exactly typed
bound renaming.**  Ten cases: the two reflexivity leaves, `symm`/`trans`, the
two congruence rules, and the four axioms. -/
theorem Equiv.rename {pureEff : ε} {n m : Nat} {β : BoundCtx τ n}
    {β' : BoundCtx τ m} (ρ : TypedRenaming β β') :
    {a b : Tm ν Φ n} → {A : τ} → Equiv pureEff Γ β a b A →
      Equiv pureEff Γ β' (Tm.rename ρ.toFun a) (Tm.rename ρ.toFun b) A
  | _, _, _, .var h => .var h
  | _, _, _, .bvar (i := i) => ρ.typed i ▸ Equiv.bvar
  | _, _, _, .symm h => .symm (Equiv.rename ρ h)
  | _, _, _, .trans h k => .trans (Equiv.rename ρ h) (Equiv.rename ρ k)
  | _, _, _, .op h => .op (Equiv.rename ρ h)
  | _, _, _, .let₁ ha hb => .let₁ (Equiv.rename ρ ha) (Equiv.rename (ρ.up _) hb)
  | _, _, _, .letBeta hp ha hb => by
      simpa using Equiv.letBeta (hp.rename ρ.toFun) (ha.rename ρ)
        (hb.rename (ρ.up _))
  | _, _, _, .letEta ha => by
      simpa using Equiv.letEta (pureEff := pureEff) (ha.rename ρ)
  | _, _, _, .bindOp ha hc => by
      simpa using Equiv.bindOp (pureEff := pureEff) (ha.rename ρ)
        (hc.rename (ρ.up _))
  | _, _, _, .bindLet ha hb hc => by
      simpa using Equiv.bindLet (pureEff := pureEff) (ha.rename ρ)
        (hb.rename (ρ.up _)) (hc.rename (ρ.up _))

end Isotope.LambdaSeq.LocallyNameless
