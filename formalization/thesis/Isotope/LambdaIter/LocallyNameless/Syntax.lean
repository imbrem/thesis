import Isotope.LambdaIter.Ty

namespace Isotope.LambdaIter.LocallyNameless

/-- A typed instruction signature.  Effects are kept abstract; `IsPure` is the
side condition used by the pure substitution equations. -/
structure Signature (τ : Type u) where
  Instr : Type v
  src : Instr → τ
  trg : Instr → τ
  IsPure : Instr → Prop := fun _ => False

/-- Locally nameless terms with `n` in-scope bound variables. -/
inductive Tm (ν : Type w) (𝕀 : Type v) : Nat → Type (max v w) where
  | fv {n} (x : ν) : Tm ν 𝕀 n
  | bv {n} (ι : Fin n) : Tm ν 𝕀 n
  | op {n} (f : 𝕀) (a : Tm ν 𝕀 n) : Tm ν 𝕀 n
  | let₁ {n} (a : Tm ν 𝕀 n) (b : Tm ν 𝕀 (n + 1)) : Tm ν 𝕀 n
  | unit {n} : Tm ν 𝕀 n
  | pair {n} (a b : Tm ν 𝕀 n) : Tm ν 𝕀 n
  | let₂ {n} (a : Tm ν 𝕀 n) (b : Tm ν 𝕀 (n + 2)) : Tm ν 𝕀 n
  | inl {n} (a : Tm ν 𝕀 n) : Tm ν 𝕀 n
  | inr {n} (a : Tm ν 𝕀 n) : Tm ν 𝕀 n
  | case {n} (e : Tm ν 𝕀 n) (l r : Tm ν 𝕀 (n + 1)) : Tm ν 𝕀 n
  | abort {n} (a : Tm ν 𝕀 n) : Tm ν 𝕀 n
  | iter {n} (init : Tm ν 𝕀 n) (body : Tm ν 𝕀 (n + 1)) : Tm ν 𝕀 n
  deriving Repr

namespace Tm

private def up (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

/-- Rename bound variables. -/
def rename (ρ : Fin n → Fin m) : Tm ν 𝕀 n → Tm ν 𝕀 m
  | .fv x => .fv x
  | .bv i => .bv (ρ i)
  | .op f a => .op f (rename ρ a)
  | .let₁ a b => .let₁ (rename ρ a) (rename (up ρ) b)
  | .unit => .unit
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .let₂ a b => .let₂ (rename ρ a) (rename (up (up ρ)) b)
  | .inl a => .inl (rename ρ a)
  | .inr a => .inr (rename ρ a)
  | .case e l r => .case (rename ρ e) (rename (up ρ) l) (rename (up ρ) r)
  | .abort a => .abort (rename ρ a)
  | .iter a b => .iter (rename ρ a) (rename (up ρ) b)

def lift (t : Tm ν 𝕀 n) : Tm ν 𝕀 (n + 1) := rename Fin.succ t

/-- Insert one ambient binder under the top binder, preserving index zero. -/
def underBinder (t : Tm ν 𝕀 (n + 1)) : Tm ν 𝕀 (n + 2) :=
  rename (Fin.cases 0 (fun i => Fin.succ (Fin.succ i))) t

/-- Insert one ambient binder under the top two binders. -/
def underTwoBinders (t : Tm ν 𝕀 (n + 2)) : Tm ν 𝕀 (n + 3) :=
  rename (Fin.cases 0 (Fin.cases 1 (fun i => Fin.succ (Fin.succ (Fin.succ i))))) t

private def upSub (σ : Fin n → Tm ν 𝕀 m) : Fin (n + 1) → Tm ν 𝕀 (m + 1) :=
  Fin.cases (.bv 0) (fun i => lift (σ i))

/-- Simultaneous, capture-avoiding substitution for bound variables. -/
def bsubst (σ : Fin n → Tm ν 𝕀 m) : Tm ν 𝕀 n → Tm ν 𝕀 m
  | .fv x => .fv x
  | .bv i => σ i
  | .op f a => .op f (bsubst σ a)
  | .let₁ a b => .let₁ (bsubst σ a) (bsubst (upSub σ) b)
  | .unit => .unit
  | .pair a b => .pair (bsubst σ a) (bsubst σ b)
  | .let₂ a b => .let₂ (bsubst σ a) (bsubst (upSub (upSub σ)) b)
  | .inl a => .inl (bsubst σ a)
  | .inr a => .inr (bsubst σ a)
  | .case e l r => .case (bsubst σ e) (bsubst (upSub σ) l) (bsubst (upSub σ) r)
  | .abort a => .abort (bsubst σ a)
  | .iter a b => .iter (bsubst σ a) (bsubst (upSub σ) b)

/-- Open the outermost binder. -/
def instantiate (b : Tm ν 𝕀 (n + 1)) (a : Tm ν 𝕀 n) : Tm ν 𝕀 n :=
  bsubst (Fin.cases a (fun i => .bv i)) b

/-- Substitute a term for a free variable. -/
def fsubst [DecidableEq ν] (x : ν) (s : Tm ν 𝕀 n) : Tm ν 𝕀 n → Tm ν 𝕀 n
  | .fv y => if x = y then s else .fv y
  | .bv i => .bv i
  | .op f a => .op f (fsubst x s a)
  | .let₁ a b => .let₁ (fsubst x s a) (fsubst x (lift s) b)
  | .unit => .unit
  | .pair a b => .pair (fsubst x s a) (fsubst x s b)
  | .let₂ a b => .let₂ (fsubst x s a) (fsubst x (lift (lift s)) b)
  | .inl a => .inl (fsubst x s a)
  | .inr a => .inr (fsubst x s a)
  | .case e l r => .case (fsubst x s e) (fsubst x (lift s) l) (fsubst x (lift s) r)
  | .abort a => .abort (fsubst x s a)
  | .iter a b => .iter (fsubst x s a) (fsubst x (lift s) b)

@[simp] theorem fsubst_fv_self [DecidableEq ν] (x : ν) (s : Tm ν 𝕀 n) :
    fsubst x s (.fv x) = s := by simp [fsubst]

@[simp] theorem fsubst_fv_ne [DecidableEq ν] {x y : ν} (h : x ≠ y) (s : Tm ν 𝕀 n) :
    fsubst x s (.fv y) = .fv y := by simp [fsubst, h]

end Tm
end Isotope.LambdaIter.LocallyNameless
