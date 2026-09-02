import Isotope.LambdaIter.LocallyNameless.Syntax
import Isotope.LambdaIter.Named.Defs

/-! # Lambda-case syntax and its inclusion into lambda-iter -/

namespace Isotope.LambdaCase

namespace Named

abbrev Binder (ν : Type u) := Option ν

/-- Named lambda-case terms. -/
inductive Tm (ν : Type u) (Φ : Type v) where
  | var (x : ν)
  | op (f : Φ) (a : Tm ν Φ)
  | let₁ (x : Binder ν) (a b : Tm ν Φ)
  | unit
  | pair (a b : Tm ν Φ)
  | let₂ (x y : Binder ν) (a b : Tm ν Φ)
  | inl (a : Tm ν Φ)
  | inr (a : Tm ν Φ)
  | case (e : Tm ν Φ) (x : Binder ν) (a : Tm ν Φ)
      (y : Binder ν) (b : Tm ν Φ)
  | abort (a : Tm ν Φ)
  deriving Repr

/-- The constructor-preserving inclusion of named lambda-case terms. -/
def embed : Tm ν Φ → LambdaIter.Named.Tm ν Φ
  | .var x => .var x
  | .op f a => .op f (embed a)
  | .let₁ x a b => .let₁ x (embed a) (embed b)
  | .unit => .unit
  | .pair a b => .pair (embed a) (embed b)
  | .let₂ x y a b => .let₂ x y (embed a) (embed b)
  | .inl a => .inl (embed a)
  | .inr a => .inr (embed a)
  | .case e x a y b => .case (embed e) x (embed a) y (embed b)
  | .abort a => .abort (embed a)

private def unembed : LambdaIter.Named.Tm ν Φ → Option (Tm ν Φ)
  | .var x => some (.var x)
  | .op f a => return .op f (← unembed a)
  | .let₁ x a b => return .let₁ x (← unembed a) (← unembed b)
  | .unit => some .unit
  | .pair a b => return .pair (← unembed a) (← unembed b)
  | .let₂ x y a b => return .let₂ x y (← unembed a) (← unembed b)
  | .inl a => return .inl (← unembed a)
  | .inr a => return .inr (← unembed a)
  | .case e x a y b => return .case (← unembed e) x (← unembed a) y (← unembed b)
  | .abort a => return .abort (← unembed a)
  | .iter _ _ _ => none

private theorem unembed_embed (t : Tm ν Φ) : unembed (embed t) = some t := by
  induction t <;> simp [embed, unembed, *]

theorem embed_injective : Function.Injective (embed : Tm ν Φ → LambdaIter.Named.Tm ν Φ) := by
  intro a b h
  have h' := congrArg unembed h
  exact Option.some.inj (by simpa only [unembed_embed] using h')

end Named

namespace LocallyNameless

/-- Locally nameless lambda-case terms with `n` bound variables. -/
inductive Tm (ν : Type w) (Φ : Type v) : Nat → Type (max v w) where
  | fv {n} (x : ν) : Tm ν Φ n
  | bv {n} (i : Fin n) : Tm ν Φ n
  | op {n} (f : Φ) (a : Tm ν Φ n) : Tm ν Φ n
  | let₁ {n} (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) : Tm ν Φ n
  | unit {n} : Tm ν Φ n
  | pair {n} (a b : Tm ν Φ n) : Tm ν Φ n
  | let₂ {n} (a : Tm ν Φ n) (b : Tm ν Φ (n + 2)) : Tm ν Φ n
  | inl {n} (a : Tm ν Φ n) : Tm ν Φ n
  | inr {n} (a : Tm ν Φ n) : Tm ν Φ n
  | case {n} (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) : Tm ν Φ n
  | abort {n} (a : Tm ν Φ n) : Tm ν Φ n
  deriving Repr

namespace Tm

private def up (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

def rename (ρ : Fin n → Fin m) : Tm ν Φ n → Tm ν Φ m
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

def lift (t : Tm ν Φ n) : Tm ν Φ (n + 1) := rename Fin.succ t

def underBinder (t : Tm ν Φ (n + 1)) : Tm ν Φ (n + 2) :=
  rename (Fin.cases 0 (fun i => Fin.succ (Fin.succ i))) t

def underTwoBinders (t : Tm ν Φ (n + 2)) : Tm ν Φ (n + 3) :=
  rename (Fin.cases 0 (Fin.cases 1 (fun i => Fin.succ (Fin.succ (Fin.succ i))))) t

private def upSub (σ : Fin n → Tm ν Φ m) : Fin (n + 1) → Tm ν Φ (m + 1) :=
  Fin.cases (.bv 0) (fun i => lift (σ i))

def bsubst (σ : Fin n → Tm ν Φ m) : Tm ν Φ n → Tm ν Φ m
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

def instantiate (b : Tm ν Φ (n + 1)) (a : Tm ν Φ n) : Tm ν Φ n :=
  bsubst (Fin.cases a (fun i => .bv i)) b

/-- The constructor-preserving inclusion into locally nameless lambda-iter. -/
def embed : Tm ν Φ n → LambdaIter.LocallyNameless.Tm ν Φ n
  | .fv x => .fv x
  | .bv i => .bv i
  | .op f a => .op f (embed a)
  | .let₁ a b => .let₁ (embed a) (embed b)
  | .unit => .unit
  | .pair a b => .pair (embed a) (embed b)
  | .let₂ a b => .let₂ (embed a) (embed b)
  | .inl a => .inl (embed a)
  | .inr a => .inr (embed a)
  | .case e l r => .case (embed e) (embed l) (embed r)
  | .abort a => .abort (embed a)

@[simp] theorem embed_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    embed (rename ρ t) = LambdaIter.LocallyNameless.Tm.rename ρ (embed t) := by
  induction t generalizing m <;>
    simp [rename, embed, LambdaIter.LocallyNameless.Tm.rename, *]
  case let₁ =>
    apply congrArg (fun f => LambdaIter.LocallyNameless.Tm.rename f _)
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  case let₂ =>
    apply congrArg (fun f => LambdaIter.LocallyNameless.Tm.rename f _)
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun _ => rfl) i
  case case =>
    constructor <;>
      apply congrArg (fun f => LambdaIter.LocallyNameless.Tm.rename f _ ) <;>
      funext i <;> exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem embed_lift (t : Tm ν Φ n) :
    embed (lift t) = LambdaIter.LocallyNameless.Tm.lift (embed t) := embed_rename _ _

@[simp] theorem embed_underBinder (t : Tm ν Φ (n + 1)) :
    embed (underBinder t) = LambdaIter.LocallyNameless.Tm.underBinder (embed t) := embed_rename _ _

@[simp] theorem embed_underTwoBinders (t : Tm ν Φ (n + 2)) :
    embed (underTwoBinders t) = LambdaIter.LocallyNameless.Tm.underTwoBinders (embed t) := embed_rename _ _

@[simp] theorem embed_bsubst (σ : Fin n → Tm ν Φ m) (t : Tm ν Φ n) :
    embed (bsubst σ t) =
      LambdaIter.LocallyNameless.Tm.bsubst (fun i => embed (σ i)) (embed t) := by
  induction t generalizing m <;>
    simp [bsubst, embed, LambdaIter.LocallyNameless.Tm.bsubst, upSub, *]
  case let₁ =>
    apply congrArg (fun f => LambdaIter.LocallyNameless.Tm.bsubst f _)
    funext i
    exact Fin.cases rfl (fun _ => embed_lift _) i
  case let₂ =>
    apply congrArg (fun f => LambdaIter.LocallyNameless.Tm.bsubst f _)
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun x => ?_) i
    change embed (lift (lift (σ x))) =
      LambdaIter.LocallyNameless.Tm.lift (LambdaIter.LocallyNameless.Tm.lift (embed (σ x)))
    simp only [embed_lift]
  case case =>
    constructor <;>
      apply congrArg (fun f => LambdaIter.LocallyNameless.Tm.bsubst f _) <;>
      funext i <;> exact Fin.cases rfl (fun _ => embed_lift _) i

@[simp] theorem embed_instantiate (b : Tm ν Φ (n + 1)) (a : Tm ν Φ n) :
    embed (instantiate b a) =
      LambdaIter.LocallyNameless.Tm.instantiate (embed b) (embed a) := by
  simp [instantiate, LambdaIter.LocallyNameless.Tm.instantiate]
  apply congrArg (fun f => LambdaIter.LocallyNameless.Tm.bsubst f _)
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private def unembed : {n : Nat} → LambdaIter.LocallyNameless.Tm ν Φ n → Option (Tm ν Φ n)
  | _, .fv x => some (.fv x)
  | _, .bv i => some (.bv i)
  | _, .op f a => return .op f (← unembed a)
  | _, .let₁ a b => return .let₁ (← unembed a) (← unembed b)
  | _, .unit => some .unit
  | _, .pair a b => return .pair (← unembed a) (← unembed b)
  | _, .let₂ a b => return .let₂ (← unembed a) (← unembed b)
  | _, .inl a => return .inl (← unembed a)
  | _, .inr a => return .inr (← unembed a)
  | _, .case e l r => return .case (← unembed e) (← unembed l) (← unembed r)
  | _, .abort a => return .abort (← unembed a)
  | _, .iter _ _ => none

private theorem unembed_embed (t : Tm ν Φ n) : unembed (embed t) = some t := by
  induction t <;> simp [embed, unembed, *]

theorem embed_injective : Function.Injective (embed : Tm ν Φ n → _) := by
  intro a b h
  have h' := congrArg unembed h
  exact Option.some.inj (by simpa only [unembed_embed] using h')

end Tm
end LocallyNameless
end Isotope.LambdaCase
