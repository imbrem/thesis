import Isotope.LambdaIter.NoSubtyping.Metatheory.Syntax

/-! Renaming and substitution of the complete no-subtyping equality theory. -/

namespace Isotope.LambdaIter.NoSubtyping.LocallyNameless

open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.LocallyNameless.Tm
open Syntax

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] {pureEff : ε}
variable {Γ : LambdaIter.Ctx ν τ}

namespace Pure

/-- Syntactic purity is stable under arbitrary bound renaming. -/
def rename (ρ : Fin n → Fin m) : {a : Tm ν Φ n} →
    Pure pureEff a → Pure pureEff (Tm.rename ρ a)
  | _, .fv => .fv
  | _, .bv => .bv
  | _, .op hf h => .op hf (rename ρ h)
  | _, .let₁ ha hb => .let₁ (rename ρ ha) (rename (upRen ρ) hb)
  | _, .unit => .unit
  | _, .pair ha hb => .pair (rename ρ ha) (rename ρ hb)
  | _, .let₂ ha hb => .let₂ (rename ρ ha) (rename (upRen (upRen ρ)) hb)
  | _, .inl h => .inl (rename ρ h)
  | _, .inr h => .inr (rename ρ h)
  | _, .case he hl hr =>
      .case (rename ρ he) (rename (upRen ρ) hl) (rename (upRen ρ) hr)
  | _, .abort h => .abort (rename ρ h)

/-- A simultaneous substitution preserves purity exactly when each bound
variable image is pure.  Pointwise purity is necessary because bound
variables themselves are pure, and sufficient by structural induction. -/
def PureSubst (σ : Fin n → Tm ν Φ m) : Prop :=
  ∀ i, Pure pureEff (σ i)

namespace PureSubst

def up {σ : Fin n → Tm ν Φ m} (h : PureSubst (pureEff := pureEff) σ) :
    PureSubst (pureEff := pureEff) (upSub σ) :=
  Fin.cases .bv (fun i => (h i).rename Fin.succ)

end PureSubst

/-- Pointwise-pure simultaneous substitutions preserve every syntactically
pure term. -/
def bsubst {σ : Fin n → Tm ν Φ m} (hσ : PureSubst (pureEff := pureEff) σ) :
    {a : Tm ν Φ n} → Pure pureEff a → Pure pureEff (Tm.bsubst σ a)
  | _, .fv => .fv
  | _, .bv => hσ _
  | _, .op hf h => .op hf (bsubst hσ h)
  | _, .let₁ ha hb => .let₁ (bsubst hσ ha) (bsubst hσ.up hb)
  | _, .unit => .unit
  | _, .pair ha hb => .pair (bsubst hσ ha) (bsubst hσ hb)
  | _, .let₂ ha hb => .let₂ (bsubst hσ ha) (bsubst hσ.up.up hb)
  | _, .inl h => .inl (bsubst hσ h)
  | _, .inr h => .inr (bsubst hσ h)
  | _, .case he hl hr =>
      .case (bsubst hσ he) (bsubst hσ.up hl) (bsubst hσ.up hr)
  | _, .abort h => .abort (bsubst hσ h)

end Pure

/-- The weakest uniform substitution interface preserving both the typed and
pure fragments: exact typing for every image and purity for every image. -/
structure PureTypedSubst {n m : Nat} (β : BoundCtx τ n) (β' : BoundCtx τ m)
    (σ : Fin n → Tm ν Φ m) where
  typed : TypedSubst (Γ := Γ) β β' σ
  pure : Pure.PureSubst (pureEff := pureEff) σ

namespace PureTypedSubst

def up {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m}
    (s : PureTypedSubst (Γ := Γ) (pureEff := pureEff) β β' σ)
    (A : τ) :
    PureTypedSubst (Γ := Γ) (pureEff := pureEff)
      (.snoc β A) (.snoc β' A) (upSub σ) where
  typed := s.typed.up A
  pure := s.pure.up

/-- Substitution interfaces compose in the same order as raw simultaneous
substitutions. -/
def comp {n m k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {β'' : BoundCtx τ k} {σ : Fin n → Tm ν Φ m} {θ : Fin m → Tm ν Φ k}
    (s : PureTypedSubst (Γ := Γ) (pureEff := pureEff) β β' σ)
    (t : PureTypedSubst (Γ := Γ) (pureEff := pureEff) β' β'' θ) :
    PureTypedSubst (Γ := Γ) (pureEff := pureEff)
      β β'' (fun i => Tm.bsubst θ (σ i)) where
  typed := fun i => HasType.bsubst t.typed (s.typed i)
  pure := fun i => Pure.bsubst t.pure (s.pure i)

/-- Opening substitution for the newest binder. -/
def inst {n : Nat} {β : BoundCtx τ n} {A : τ} {a : Tm ν Φ n}
    (ha : HasType Φ Γ β a A) (hp : Pure pureEff a) :
    PureTypedSubst (Γ := Γ) (pureEff := pureEff) (.snoc β A) β
      (Fin.cases a (fun i => .bv i)) where
  typed := Fin.cases ha (fun _ => .bv)
  pure := Fin.cases hp (fun _ => .bv)

end PureTypedSubst

namespace StructuralAxiom

def rename (ρ : Fin n → Fin m) : {a b : Tm ν Φ n} →
    StructuralAxiom pureEff a b →
      StructuralAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b)
  | _, _, .letBeta hp => by
      simpa using StructuralAxiom.letBeta (hp.rename ρ)
  | _, _, .letEta _ => .letEta _
  | _, _, .unitEta _ => .unitEta _
  | _, _, .pairBeta _ _ _ => by
      simpa using StructuralAxiom.pairBeta (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename ρ _) (Tm.rename (upRen (upRen ρ)) _)
  | _, _, .pairEta _ => .pairEta _
  | _, _, .caseBetaL _ _ _ => .caseBetaL _ _ _
  | _, _, .caseBetaR _ _ _ => .caseBetaR _ _ _
  | _, _, .caseEta _ => .caseEta _
  | _, _, .emptyInitial _ _ _ => .emptyInitial _ _ _

def bsubst {σ : Fin n → Tm ν Φ m} (hσ : Pure.PureSubst (pureEff := pureEff) σ) :
    {a b : Tm ν Φ n} → StructuralAxiom pureEff a b →
      StructuralAxiom pureEff (Tm.bsubst σ a) (Tm.bsubst σ b)
  | _, _, .letBeta hp => by
      simpa using StructuralAxiom.letBeta (hp.bsubst hσ)
  | _, _, .letEta _ => .letEta _
  | _, _, .unitEta _ => .unitEta _
  | _, _, .pairBeta _ _ _ => by
      simpa using StructuralAxiom.pairBeta (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst σ _) (Tm.bsubst (upSub (upSub σ)) _)
  | _, _, .pairEta _ => .pairEta _
  | _, _, .caseBetaL _ _ _ => .caseBetaL _ _ _
  | _, _, .caseBetaR _ _ _ => .caseBetaR _ _ _
  | _, _, .caseEta _ => .caseEta _
  | _, _, .emptyInitial _ _ _ => .emptyInitial _ _ _

end StructuralAxiom

namespace SequencingAxiom

def rename (ρ : Fin n → Fin m) : {a b : Tm ν Φ n} →
    SequencingAxiom pureEff a b →
      SequencingAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b)
  | _, _, .bindOp _ _ => by
      simpa using SequencingAxiom.bindOp (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _)
  | _, _, .bindLet _ _ _ => by
      simpa using SequencingAxiom.bindLet (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _) (Tm.rename (upRen ρ) _)
  | _, _, .bindLetPair _ _ _ => by
      simpa using SequencingAxiom.bindLetPair (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen (upRen ρ)) _) (Tm.rename (upRen ρ) _)
  | _, _, .bindLetCase _ _ _ _ => by
      simpa using SequencingAxiom.bindLetCase (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _) (Tm.rename (upRen ρ) _)
        (Tm.rename (upRen ρ) _)
  | _, _, .bindPair _ _ => by
      simpa using SequencingAxiom.bindPair (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen (upRen ρ)) _)
  | _, _, .bindCase _ _ _ => by
      simpa using SequencingAxiom.bindCase (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _) (Tm.rename (upRen ρ) _)

def bsubst (σ : Fin n → Tm ν Φ m) : {a b : Tm ν Φ n} →
    SequencingAxiom pureEff a b →
      SequencingAxiom pureEff (Tm.bsubst σ a) (Tm.bsubst σ b)
  | _, _, .bindOp _ _ => by
      simpa using SequencingAxiom.bindOp (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst (upSub σ) _)
  | _, _, .bindLet _ _ _ => by
      simpa using SequencingAxiom.bindLet (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst (upSub σ) _) (Tm.bsubst (upSub σ) _)
  | _, _, .bindLetPair _ _ _ => by
      simpa using SequencingAxiom.bindLetPair (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst (upSub (upSub σ)) _) (Tm.bsubst (upSub σ) _)
  | _, _, .bindLetCase _ _ _ _ => by
      simpa using SequencingAxiom.bindLetCase (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst (upSub σ) _) (Tm.bsubst (upSub σ) _)
        (Tm.bsubst (upSub σ) _)
  | _, _, .bindPair _ _ => by
      simpa using SequencingAxiom.bindPair (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst (upSub (upSub σ)) _)
  | _, _, .bindCase _ _ _ => by
      simpa using SequencingAxiom.bindCase (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst (upSub σ) _) (Tm.bsubst (upSub σ) _)

end SequencingAxiom

namespace IterationAxiom

def rename (ρ : Fin n → Fin m) : {a b : Tm ν Φ n} →
    IterationAxiom pureEff a b →
      IterationAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b)
  | _, _, .fixpoint _ _ => by
      simpa using IterationAxiom.fixpoint (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _)
  | _, _, .naturality _ _ _ => by
      simpa using IterationAxiom.naturality (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _) (Tm.rename (upRen ρ) _)
  | _, _, .codiagonal _ _ => by
      simpa using IterationAxiom.codiagonal (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _)
  | _, _, .iterBind _ _ => by
      simpa using IterationAxiom.iterBind (pureEff := pureEff)
        (Tm.rename ρ _) (Tm.rename (upRen ρ) _)

def bsubst (σ : Fin n → Tm ν Φ m) : {a b : Tm ν Φ n} →
    IterationAxiom pureEff a b →
      IterationAxiom pureEff (Tm.bsubst σ a) (Tm.bsubst σ b)
  | _, _, .fixpoint _ _ => by
      simpa using IterationAxiom.fixpoint (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst (upSub σ) _)
  | _, _, .naturality _ _ _ => by
      simpa using IterationAxiom.naturality (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst (upSub σ) _) (Tm.bsubst (upSub σ) _)
  | _, _, .codiagonal _ _ => by
      simpa using IterationAxiom.codiagonal (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst (upSub σ) _)
  | _, _, .iterBind _ _ => by
      simpa using IterationAxiom.iterBind (pureEff := pureEff)
        (Tm.bsubst σ _) (Tm.bsubst (upSub σ) _)

end IterationAxiom

namespace CoreAxiom

def rename (ρ : Fin n → Fin m) : {a b : Tm ν Φ n} → CoreAxiom pureEff a b →
    CoreAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b)
  | _, _, .structural h => .structural (h.rename ρ)
  | _, _, .sequencing h => .sequencing (h.rename ρ)
  | _, _, .iteration h => .iteration (h.rename ρ)

def bsubst {σ : Fin n → Tm ν Φ m} (hσ : Pure.PureSubst (pureEff := pureEff) σ) :
    {a b : Tm ν Φ n} → CoreAxiom pureEff a b →
      CoreAxiom pureEff (Tm.bsubst σ a) (Tm.bsubst σ b)
  | _, _, .structural h => .structural (h.bsubst hσ)
  | _, _, .sequencing h => .sequencing (h.bsubst σ)
  | _, _, .iteration h => .iteration (h.bsubst σ)

end CoreAxiom

namespace Eqv

/-- The complete typed equational theory is stable under every pointwise-pure,
exactly typed simultaneous substitution. -/
def bsubst {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m}
    (s : PureTypedSubst (Γ := Γ) (pureEff := pureEff) β β' σ) :
    {a b : Tm ν Φ n} → {A : τ} → Eqv pureEff Γ β a b A →
      Eqv pureEff Γ β' (Tm.bsubst σ a) (Tm.bsubst σ b) A
  | _, _, _, .refl h => .refl (HasType.bsubst s.typed h)
  | _, _, _, .symm h => .symm (bsubst s h)
  | _, _, _, .trans h k => .trans (bsubst s h) (bsubst s k)
  | _, _, _, .op h => .op (bsubst s h)
  | _, _, _, .let₁ ha hb => .let₁ (bsubst s ha) (bsubst (s.up _) hb)
  | _, _, _, .unit => .unit
  | _, _, _, .pair ha hb => .pair (bsubst s ha) (bsubst s hb)
  | _, _, _, .let₂ he hc => .let₂ (bsubst s he) (bsubst ((s.up _).up _) hc)
  | _, _, _, .inl h => .inl (bsubst s h)
  | _, _, _, .inr h => .inr (bsubst s h)
  | _, _, _, .case he hl hr =>
      .case (bsubst s he) (bsubst (s.up _) hl) (bsubst (s.up _) hr)
  | _, _, _, .abort h => .abort (bsubst s h)
  | _, _, _, .iter ha hb => .iter (bsubst s ha) (bsubst (s.up _) hb)
  | _, _, _, .ax hax ha hb =>
      .ax (hax.bsubst s.pure) (HasType.bsubst s.typed ha) (HasType.bsubst s.typed hb)
  | _, _, _, .uniformity ha hh hp hb hb' square => by
      refine Eqv.uniformity
        (HasType.bsubst s.typed ha)
        (HasType.bsubst (s.typed.up _) hh)
        (hp.bsubst s.pure.up)
        (HasType.bsubst (s.typed.up _) hb)
        (HasType.bsubst (s.typed.up _) hb')
        ?_
      convert bsubst (s.up _) square using 1 <;>
        simp only [Syntax.bsubst_case, Syntax.bsubst_inl, Syntax.bsubst_inr,
          Syntax.bsubst_bv, Syntax.bsubst_underBinder,
          Syntax.bsubst_instantiate, Syntax.upSub_zero] <;>
        congr 1

/-- Opening the newest binder by a pure term preserves the complete typed
equational theory.  Purity is necessary because opening can substitute into
the purity premise of `letBeta`. -/
def instantiate {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)}
    (h : Eqv pureEff Γ (.snoc β A) b b' B)
    (ha : HasType Φ Γ β a A) (hp : Pure pureEff a) :
    Eqv pureEff Γ β (Tm.instantiate b a) (Tm.instantiate b' a) B :=
  bsubst (PureTypedSubst.inst ha hp) h

/-- The complete typed equational theory is stable under every exactly typed
bound-variable renaming. -/
def rename {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    (ρ : TypedRenaming β β') :
    {a b : Tm ν Φ n} → {A : τ} → Eqv pureEff Γ β a b A →
      Eqv pureEff Γ β' (Tm.rename ρ.toFun a) (Tm.rename ρ.toFun b) A
  | _, _, _, .refl h => .refl (HasType.rename ρ h)
  | _, _, _, .symm h => .symm (rename ρ h)
  | _, _, _, .trans h k => .trans (rename ρ h) (rename ρ k)
  | _, _, _, .op h => .op (rename ρ h)
  | _, _, _, .let₁ ha hb => .let₁ (rename ρ ha) (rename (ρ.up _) hb)
  | _, _, _, .unit => .unit
  | _, _, _, .pair ha hb => .pair (rename ρ ha) (rename ρ hb)
  | _, _, _, .let₂ he hc => .let₂ (rename ρ he) (rename ((ρ.up _).up _) hc)
  | _, _, _, .inl h => .inl (rename ρ h)
  | _, _, _, .inr h => .inr (rename ρ h)
  | _, _, _, .case he hl hr =>
      .case (rename ρ he) (rename (ρ.up _) hl) (rename (ρ.up _) hr)
  | _, _, _, .abort h => .abort (rename ρ h)
  | _, _, _, .iter ha hb => .iter (rename ρ ha) (rename (ρ.up _) hb)
  | _, _, _, .ax hax ha hb =>
      .ax (hax.rename ρ.toFun) (HasType.rename ρ ha) (HasType.rename ρ hb)
  | _, _, _, .uniformity ha hh hp hb hb' square => by
      refine Eqv.uniformity
        (HasType.rename ρ ha)
        (HasType.rename (ρ.up _) hh)
        (hp.rename (upRen ρ.toFun))
        (HasType.rename (ρ.up _) hb)
        (HasType.rename (ρ.up _) hb')
        ?_
      convert rename (ρ.up _) square using 1 <;>
        simp only [TypedRenaming.up, Syntax.rename_case, Syntax.rename_inl,
          Syntax.rename_inr, Syntax.rename_bv, Syntax.rename_underBinder,
          Syntax.rename_instantiate, Syntax.upRen_zero] <;>
        congr 1 <;>
        first
        | (apply Syntax.rename_congr; intro i; rfl)
        | (change (Tm.rename (upRen ρ.toFun) _).underBinder.inr =
              (Tm.rename (upRen (upRen ρ.toFun)) _).inr
           exact congrArg Tm.inr (Syntax.rename_underBinder ρ.toFun _).symm)
        | (change (Tm.rename (upRen ρ.toFun) _).underBinder =
              Tm.rename (upRen (upRen ρ.toFun)) _
           exact (Syntax.rename_underBinder ρ.toFun _).symm)

end Eqv

end Isotope.LambdaIter.NoSubtyping.LocallyNameless
