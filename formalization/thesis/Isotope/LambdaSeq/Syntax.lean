import Isotope.LambdaCase.Syntax

/-! # Lambda-seq syntax and inclusions -/

namespace Isotope.LambdaSeq

namespace Named

abbrev Binder (ν : Type u) := Option ν

/-- The sequential fragment: variables, primitive instructions, and `let`. -/
inductive Tm (ν : Type u) (Φ : Type v) where
  | var (x : ν)
  | op (f : Φ) (a : Tm ν Φ)
  | let₁ (x : Binder ν) (a b : Tm ν Φ)
  deriving Repr

def embedCase : Tm ν Φ → LambdaCase.Named.Tm ν Φ
  | .var x => .var x
  | .op f a => .op f (embedCase a)
  | .let₁ x a b => .let₁ x (embedCase a) (embedCase b)

def embedIter (t : Tm ν Φ) : LambdaIter.Named.Tm ν Φ := LambdaCase.Named.embed (embedCase t)

private def unembed : LambdaCase.Named.Tm ν Φ → Option (Tm ν Φ)
  | .var x => some (.var x)
  | .op f a => return .op f (← unembed a)
  | .let₁ x a b => return .let₁ x (← unembed a) (← unembed b)
  | _ => none

private theorem unembed_embedCase (t : Tm ν Φ) : unembed (embedCase t) = some t := by
  induction t <;> simp [embedCase, unembed, *]

theorem embedCase_injective : Function.Injective (embedCase : Tm ν Φ → _) := by
  intro a b h
  exact Option.some.inj (by simpa only [unembed_embedCase] using congrArg unembed h)

theorem embedIter_injective : Function.Injective (embedIter : Tm ν Φ → _) :=
  LambdaCase.Named.embed_injective.comp embedCase_injective

end Named

namespace LocallyNameless

inductive Tm (ν : Type w) (Φ : Type v) : Nat → Type (max v w) where
  | fv {n} (x : ν) : Tm ν Φ n
  | bv {n} (i : Fin n) : Tm ν Φ n
  | op {n} (f : Φ) (a : Tm ν Φ n) : Tm ν Φ n
  | let₁ {n} (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) : Tm ν Φ n
  deriving Repr

namespace Tm

private def up (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

def rename (ρ : Fin n → Fin m) : Tm ν Φ n → Tm ν Φ m
  | .fv x => .fv x
  | .bv i => .bv (ρ i)
  | .op f a => .op f (rename ρ a)
  | .let₁ a b => .let₁ (rename ρ a) (rename (up ρ) b)

def lift (t : Tm ν Φ n) : Tm ν Φ (n + 1) := rename Fin.succ t

def underBinder (t : Tm ν Φ (n + 1)) : Tm ν Φ (n + 2) :=
  rename (Fin.cases 0 (fun i => Fin.succ (Fin.succ i))) t

private def upSub (σ : Fin n → Tm ν Φ m) : Fin (n + 1) → Tm ν Φ (m + 1) :=
  Fin.cases (.bv 0) (fun i => lift (σ i))

def bsubst (σ : Fin n → Tm ν Φ m) : Tm ν Φ n → Tm ν Φ m
  | .fv x => .fv x
  | .bv i => σ i
  | .op f a => .op f (bsubst σ a)
  | .let₁ a b => .let₁ (bsubst σ a) (bsubst (upSub σ) b)

def instantiate (b : Tm ν Φ (n + 1)) (a : Tm ν Φ n) : Tm ν Φ n :=
  bsubst (Fin.cases a (fun i => .bv i)) b

def embedCase : Tm ν Φ n → LambdaCase.LocallyNameless.Tm ν Φ n
  | .fv x => .fv x
  | .bv i => .bv i
  | .op f a => .op f (embedCase a)
  | .let₁ a b => .let₁ (embedCase a) (embedCase b)

def embedIter (t : Tm ν Φ n) : LambdaIter.LocallyNameless.Tm ν Φ n :=
  LambdaCase.LocallyNameless.Tm.embed (embedCase t)

@[simp] theorem embedCase_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    embedCase (rename ρ t) = LambdaCase.LocallyNameless.Tm.rename ρ (embedCase t) := by
  induction t generalizing m <;> simp [rename, embedCase, LambdaCase.LocallyNameless.Tm.rename, *]
  apply congrArg (fun f => LambdaCase.LocallyNameless.Tm.rename f _)
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem embedCase_lift (t : Tm ν Φ n) :
    embedCase (lift t) = LambdaCase.LocallyNameless.Tm.lift (embedCase t) := embedCase_rename _ _

@[simp] theorem embedCase_underBinder (t : Tm ν Φ (n + 1)) :
    embedCase (underBinder t) = LambdaCase.LocallyNameless.Tm.underBinder (embedCase t) := embedCase_rename _ _

@[simp] theorem embedCase_bsubst (σ : Fin n → Tm ν Φ m) (t : Tm ν Φ n) :
    embedCase (bsubst σ t) =
      LambdaCase.LocallyNameless.Tm.bsubst (fun i => embedCase (σ i)) (embedCase t) := by
  induction t generalizing m <;>
    simp [bsubst, embedCase, LambdaCase.LocallyNameless.Tm.bsubst, upSub, *]
  apply congrArg (fun f => LambdaCase.LocallyNameless.Tm.bsubst f _)
  funext i
  exact Fin.cases rfl (fun _ => embedCase_lift _) i

@[simp] theorem embedCase_instantiate (b : Tm ν Φ (n + 1)) (a : Tm ν Φ n) :
    embedCase (instantiate b a) =
      LambdaCase.LocallyNameless.Tm.instantiate (embedCase b) (embedCase a) := by
  simp [instantiate, LambdaCase.LocallyNameless.Tm.instantiate]
  apply congrArg (fun f => LambdaCase.LocallyNameless.Tm.bsubst f _)
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private def unembed : {n : Nat} → LambdaCase.LocallyNameless.Tm ν Φ n → Option (Tm ν Φ n)
  | _, .fv x => some (.fv x)
  | _, .bv i => some (.bv i)
  | _, .op f a => return .op f (← unembed a)
  | _, .let₁ a b => return .let₁ (← unembed a) (← unembed b)
  | _, _ => none

private theorem unembed_embedCase (t : Tm ν Φ n) : unembed (embedCase t) = some t := by
  induction t <;> simp [embedCase, unembed, *]

theorem embedCase_injective : Function.Injective (embedCase : Tm ν Φ n → _) := by
  intro a b h
  exact Option.some.inj (by simpa only [unembed_embedCase] using congrArg unembed h)

theorem embedIter_injective : Function.Injective (embedIter : Tm ν Φ n → _) :=
  LambdaCase.LocallyNameless.Tm.embed_injective.comp embedCase_injective

end Tm
end LocallyNameless
end Isotope.LambdaSeq
