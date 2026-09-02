import Isotope.LambdaIter.NoSubtyping.Equiv

/-!
# Locally nameless metatheory without subtyping

Bound renamings and simultaneous substitutions carry exact type preservation.
No coercion cases or subtyping coherence hypotheses occur in these proofs.
-/

namespace Isotope.LambdaIter.NoSubtyping.LocallyNameless

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {Γ Γ' : LambdaIter.Ctx ν τ}

/-- A bound-variable renaming preserving the type at every selected slot. -/
structure TypedRenaming (β : BoundCtx τ n) (β' : BoundCtx τ m) where
  toFun : Fin n → Fin m
  typed (i : Fin n) : β'.get (toFun i) = β.get i

namespace TypedRenaming

def up (ρ : TypedRenaming β β') (A : τ) :
    TypedRenaming (.snoc β A) (.snoc β' A) where
  toFun := Fin.cases 0 (fun i => Fin.succ (ρ.toFun i))
  typed := Fin.cases rfl (fun i => ρ.typed i)

def succ (β : BoundCtx τ n) (A : τ) : TypedRenaming β (.snoc β A) where
  toFun := Fin.succ
  typed := fun _ => rfl

def underBinder (β : BoundCtx τ n) (X Y : τ) :
    TypedRenaming (.snoc β Y) (.snoc (.snoc β X) Y) where
  toFun := Fin.cases 0 (fun i => Fin.succ (Fin.succ i))
  typed := Fin.cases rfl (fun _ => rfl)

def underTwoBinders (β : BoundCtx τ n) (X Y Z : τ) :
    TypedRenaming (.snoc (.snoc β Y) Z) (.snoc (.snoc (.snoc β X) Y) Z) where
  toFun := Fin.cases 0 (Fin.cases 1 (fun i => Fin.succ (Fin.succ (Fin.succ i))))
  typed := Fin.cases rfl (Fin.cases rfl (fun _ => rfl))

end TypedRenaming

namespace HasType

def newest {n : Nat} {β : BoundCtx τ n} {A : τ} :
    HasType Φ Γ (.snoc β A) (.bv 0) A := by
  simpa [Isotope.LambdaIter.LocallyNameless.BoundCtx.get] using
    (HasType.bv (Φ := Φ) (Γ := Γ) (β := .snoc β A) (ι := (0 : Fin (n + 1))))

def previous {n : Nat} {β : BoundCtx τ n} {A B : τ} :
    HasType Φ Γ (.snoc (.snoc β A) B) (.bv 1) A := by
  simpa [Isotope.LambdaIter.LocallyNameless.BoundCtx.get] using
    (HasType.bv (Φ := Φ) (Γ := Γ) (β := .snoc (.snoc β A) B)
      (ι := (1 : Fin (n + 2))))

/-- Typing is preserved by every exactly typed bound renaming. -/
def rename {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    (ρ : TypedRenaming β β') :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β' (Isotope.LambdaIter.LocallyNameless.Tm.rename ρ.toFun t) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => ρ.typed i ▸ .bv
  | _, _, .op h => .op (rename ρ h)
  | _, _, .let₁ ha hb => .let₁ (rename ρ ha) (rename (ρ.up _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (rename ρ ha) (rename ρ hb)
  | _, _, .let₂ ha hb => .let₂ (rename ρ ha) (rename ((ρ.up _).up _) hb)
  | _, _, .inl h => .inl (rename ρ h)
  | _, _, .inr h => .inr (rename ρ h)
  | _, _, .case he hl hr =>
      .case (rename ρ he) (rename (ρ.up _) hl) (rename (ρ.up _) hr)
  | _, _, .abort h => .abort (rename ρ h)
  | _, _, .iter ha hb => .iter (rename ρ ha) (rename (ρ.up _) hb)

def lift {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (h : HasType Φ Γ β t A) :
    HasType Φ Γ (.snoc β B) (Isotope.LambdaIter.LocallyNameless.Tm.lift t) A :=
  rename (TypedRenaming.succ β B) h

def underBinder {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 1)}
    {A X Y : τ} (h : HasType Φ Γ (.snoc β Y) t A) :
    HasType Φ Γ (.snoc (.snoc β X) Y)
      (Isotope.LambdaIter.LocallyNameless.Tm.underBinder t) A :=
  rename (TypedRenaming.underBinder β X Y) h

def underTwoBinders {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 2)}
    {A X Y Z : τ} (h : HasType Φ Γ (.snoc (.snoc β Y) Z) t A) :
    HasType Φ Γ (.snoc (.snoc (.snoc β X) Y) Z)
      (Isotope.LambdaIter.LocallyNameless.Tm.underTwoBinders t) A :=
  rename (TypedRenaming.underTwoBinders β X Y Z) h

end HasType

/-- A simultaneous substitution supplying an exactly typed image for each
bound variable. -/
def TypedSubst (β : BoundCtx τ n) (β' : BoundCtx τ m)
    (σ : Fin n → Tm ν Φ m) : Type (max u q w) :=
  (i : Fin n) → HasType Φ Γ β' (σ i) (β.get i)

namespace TypedSubst

def up {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) (A : τ) :
    TypedSubst (Γ := Γ) (.snoc β A) (.snoc β' A)
      (fun i => Fin.cases (.bv (0 : Fin (m + 1)))
        (fun j => Isotope.LambdaIter.LocallyNameless.Tm.lift (σ j)) i) :=
  Fin.cases (.bv) (fun i => (s i).lift)

end TypedSubst

namespace HasType

/-- Typing is preserved by simultaneous bound substitution. -/
def bsubst {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β'
        (Isotope.LambdaIter.LocallyNameless.Tm.bsubst σ t) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => s i
  | _, _, .op h => .op (bsubst s h)
  | _, _, .let₁ ha hb => .let₁ (bsubst s ha) (bsubst (s.up _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (bsubst s ha) (bsubst s hb)
  | _, _, .let₂ ha hb => .let₂ (bsubst s ha) (bsubst ((s.up _).up _) hb)
  | _, _, .inl h => .inl (bsubst s h)
  | _, _, .inr h => .inr (bsubst s h)
  | _, _, .case he hl hr =>
      .case (bsubst s he) (bsubst (s.up _) hl) (bsubst (s.up _) hr)
  | _, _, .abort h => .abort (bsubst s h)
  | _, _, .iter ha hb => .iter (bsubst s ha) (bsubst (s.up _) hb)

/-- Opening the newest binder preserves typing. -/
def instantiate {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : HasType Φ Γ (.snoc β A) b B) (ha : HasType Φ Γ β a A) :
    HasType Φ Γ β (Isotope.LambdaIter.LocallyNameless.Tm.instantiate b a) B :=
  bsubst (σ := Fin.cases a fun i => .bv i) (Fin.cases ha fun _ => .bv) hb

end HasType

namespace Eqv

variable {ε : Type r} [HasEff Φ ε] {pureEff : ε}

/-- Equational derivations are preserved by type-preserving free weakening.
Bound contexts and terms are unchanged. -/
def weaken (hw : ∀ x A, Γ.lookup x = some A → Γ'.lookup x = some A) :
    {n : Nat} → {β : BoundCtx τ n} → {a b : Tm ν Φ n} → {A : τ} →
      Eqv pureEff Γ β a b A → Eqv pureEff Γ' β a b A
  | _, _, _, _, _, .refl h => .refl (HasType.weaken hw h)
  | _, _, _, _, _, .symm h => .symm (weaken hw h)
  | _, _, _, _, _, .trans h k => .trans (weaken hw h) (weaken hw k)
  | _, _, _, _, _, .op h => .op (weaken hw h)
  | _, _, _, _, _, .let₁ ha hb => .let₁ (weaken hw ha) (weaken hw hb)
  | _, _, _, _, _, .unit => .unit
  | _, _, _, _, _, .pair ha hb => .pair (weaken hw ha) (weaken hw hb)
  | _, _, _, _, _, .let₂ he hc => .let₂ (weaken hw he) (weaken hw hc)
  | _, _, _, _, _, .inl h => .inl (weaken hw h)
  | _, _, _, _, _, .inr h => .inr (weaken hw h)
  | _, _, _, _, _, .case he hl hr =>
      .case (weaken hw he) (weaken hw hl) (weaken hw hr)
  | _, _, _, _, _, .abort h => .abort (weaken hw h)
  | _, _, _, _, _, .iter ha hb => .iter (weaken hw ha) (weaken hw hb)
  | _, _, _, _, _, .ax hax ha hb =>
      .ax hax (HasType.weaken hw ha) (HasType.weaken hw hb)
  | _, _, _, _, _, .uniformity ha hh hp hb hb' square =>
      .uniformity (HasType.weaken hw ha) (HasType.weaken hw hh) hp
        (HasType.weaken hw hb) (HasType.weaken hw hb') (weaken hw square)

end Eqv

end Isotope.LambdaIter.NoSubtyping.LocallyNameless
