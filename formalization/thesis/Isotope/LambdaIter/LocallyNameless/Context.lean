import Isotope.LambdaIter.Weakening
import Isotope.LambdaIter.LocallyNameless.Syntax

namespace Isotope.LambdaIter.LocallyNameless

/-- Bound contexts are the anonymous-only specialization of shared snoc
contexts, indexed by their length. -/
inductive BoundCtx (τ : Type u) : Nat → Type u where
  | nil : BoundCtx τ 0
  | snoc : BoundCtx τ n → τ → BoundCtx τ (n + 1)

namespace BoundCtx

/-- The corresponding shared context. Every slot is anonymous. -/
def toCtx : BoundCtx τ n → LambdaIter.Ctx Empty τ
  | .nil => .nil
  | .snoc Γ A => .snoc Γ.toCtx none A

@[simp] theorem length_toCtx (Γ : BoundCtx τ n) : Γ.toCtx.length = n := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp [toCtx, Ctx.length, ih]

/-- Index zero is the newest snoc slot; successors walk toward older slots. -/
def get : BoundCtx τ n → Fin n → τ
  | .snoc Γ A, ι => Fin.cases A Γ.get ι

/-- Reconstruct a snoc context from its newest-first `Fin` view. -/
def ofFin : {n : Nat} → (Fin n → τ) → BoundCtx τ n
  | 0, _ => .nil
  | n + 1, f => .snoc (ofFin (fun ι => f ι.succ)) (f 0)

@[simp] theorem get_ofFin : ∀ {n : Nat} (f : Fin n → τ), (ofFin f).get = f
  | 0, f => funext fun ι => Fin.elim0 ι
  | n + 1, f => by
      funext ι
      refine Fin.cases rfl (fun j => ?_) ι
      exact congrFun (get_ofFin (fun k : Fin n => f k.succ)) j

@[simp] theorem ofFin_get (Γ : BoundCtx τ n) : ofFin Γ.get = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp [ofFin, get, ih]

/-- Precise equivalence between anonymous snoc contexts and newest-first
finite-index lookup functions. -/
def finEquiv (τ : Type u) (n : Nat) : BoundCtx τ n ≃ (Fin n → τ) where
  toFun := get
  invFun := ofFin
  left_inv := ofFin_get
  right_inv := get_ofFin

/-- Proof-relevant, same-shape bound weakening. New slot types are subtypes of
the corresponding old slots; no bound slot can be dropped or shadowed. -/
inductive Wk [TypeFormers τ] [Subtyping τ] : BoundCtx τ n → BoundCtx τ n → Type u where
  | nil : Wk .nil .nil
  | snoc : Wk Γ' Γ → Subty A' A → Wk (.snoc Γ' A') (.snoc Γ A)

def Wk.at [TypeFormers τ] [Subtyping τ] : {n : Nat} →
    {Γ' Γ : BoundCtx τ n} → Wk Γ' Γ →
    (ι : Fin n) → Subty (Γ'.get ι) (Γ.get ι)
  | 0, .nil, .nil, .nil, ι => Fin.elim0 ι
  | _ + 1, .snoc _ _, .snoc _ _, .snoc w h, ι =>
      Fin.cases h (fun j => w.at j) ι

/-- Proposition-truncated bound weakening, exposed separately. -/
abbrev WkProp (Γ' Γ : BoundCtx τ n) [TypeFormers τ] [Subtyping τ] : Prop :=
  Nonempty (Wk Γ' Γ)

end BoundCtx

/-- Proof-relevant lookup transport for one visible free variable. -/
structure LookupRefines {ν : Type u} {τ : Type v}
    [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
    (Γ : LambdaIter.Ctx ν τ) (x : ν) (A : τ) : Type (max u v) where
  ty : τ
  found : Γ.lookup x = some ty
  subty : Subty ty A

/-- A shared free-context weakening together with exactly the lookup transport
needed by typing. Bare `SubtypeWk` permits incompatible newly shadowing names;
this wrapper deliberately rejects those derivations. -/
structure FreeWk {ν : Type u} {τ : Type v}
    [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
    (Γ' Γ : LambdaIter.Ctx ν τ) : Type (max u v) where
  structural : LambdaIter.Ctx.SubtypeWk Γ' Γ
  lookup : ∀ x A, Γ.lookup x = some A → LookupRefines Γ' x A

/-- Proposition-truncated free weakening, exposed separately. -/
abbrev FreeWkProp [DecidableEq ν] [TypeFormers τ] [Subtyping τ]
    (Γ' Γ : LambdaIter.Ctx ν τ) : Prop := Nonempty (FreeWk Γ' Γ)

end Isotope.LambdaIter.LocallyNameless
