import Isotope.LambdaIter.Metatheory.EquivSubst

/-!
# Relabelling the instructions of a term

A map of instruction sets `φ : Φ → Ψ` acts on raw locally nameless terms by
relabelling every `op` node.  This file supplies that action and its
commutation with the whole renaming/substitution algebra, together with its
action on syntactic purity and on the three raw axiom schemes.

Nothing here mentions typing: the raw syntax is parameterized by `Φ` alone.
The typed half — `HasType.map` and `Eqv.map` for a signature morphism — is in
`Isotope/LambdaIter/Models/SigAction.lean`, because it needs the type and
effect components of a morphism as well.

## Shared-namespace note

`Tm.mapInstr` and its lemmas live in the shared namespace
`Isotope.LambdaIter.LocallyNameless`.
-/

namespace Isotope.LambdaIter.LocallyNameless

open Isotope.LambdaIter.LocallyNameless.Tm

universe u v w q q'

variable {ν : Type w} {Φ : Type q} {Ψ : Type q'} {n m : Nat}

namespace Tm

/-- Relabel every instruction of a term. -/
def mapInstr (φ : Φ → Ψ) : {n : Nat} → Tm ν Φ n → Tm ν Ψ n
  | _, .fv x => .fv x
  | _, .bv i => .bv i
  | _, .op f a => .op (φ f) (mapInstr φ a)
  | _, .let₁ a b => .let₁ (mapInstr φ a) (mapInstr φ b)
  | _, .unit => .unit
  | _, .pair a b => .pair (mapInstr φ a) (mapInstr φ b)
  | _, .let₂ a b => .let₂ (mapInstr φ a) (mapInstr φ b)
  | _, .inl a => .inl (mapInstr φ a)
  | _, .inr a => .inr (mapInstr φ a)
  | _, .case e l r => .case (mapInstr φ e) (mapInstr φ l) (mapInstr φ r)
  | _, .abort a => .abort (mapInstr φ a)
  | _, .iter a b => .iter (mapInstr φ a) (mapInstr φ b)

@[simp] theorem mapInstr_fv (φ : Φ → Ψ) (x : ν) :
    mapInstr (n := n) φ (.fv x) = .fv x := rfl
@[simp] theorem mapInstr_bv (φ : Φ → Ψ) (i : Fin n) :
    mapInstr (ν := ν) φ (.bv i) = .bv i := rfl
@[simp] theorem mapInstr_op (φ : Φ → Ψ) (f : Φ) (a : Tm ν Φ n) :
    mapInstr φ (.op f a) = .op (φ f) (mapInstr φ a) := rfl
@[simp] theorem mapInstr_let₁ (φ : Φ → Ψ) (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
    mapInstr φ (.let₁ a b) = .let₁ (mapInstr φ a) (mapInstr φ b) := rfl
@[simp] theorem mapInstr_unit (φ : Φ → Ψ) :
    mapInstr (ν := ν) (n := n) φ .unit = .unit := rfl
@[simp] theorem mapInstr_pair (φ : Φ → Ψ) (a b : Tm ν Φ n) :
    mapInstr φ (.pair a b) = .pair (mapInstr φ a) (mapInstr φ b) := rfl
@[simp] theorem mapInstr_let₂ (φ : Φ → Ψ) (a : Tm ν Φ n) (b : Tm ν Φ (n + 2)) :
    mapInstr φ (.let₂ a b) = .let₂ (mapInstr φ a) (mapInstr φ b) := rfl
@[simp] theorem mapInstr_inl (φ : Φ → Ψ) (a : Tm ν Φ n) :
    mapInstr φ (.inl a) = .inl (mapInstr φ a) := rfl
@[simp] theorem mapInstr_inr (φ : Φ → Ψ) (a : Tm ν Φ n) :
    mapInstr φ (.inr a) = .inr (mapInstr φ a) := rfl
@[simp] theorem mapInstr_case (φ : Φ → Ψ) (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
    mapInstr φ (.case e l r) =
      .case (mapInstr φ e) (mapInstr φ l) (mapInstr φ r) := rfl
@[simp] theorem mapInstr_abort (φ : Φ → Ψ) (a : Tm ν Φ n) :
    mapInstr φ (.abort a) = .abort (mapInstr φ a) := rfl
@[simp] theorem mapInstr_iter (φ : Φ → Ψ) (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
    mapInstr φ (.iter a b) = .iter (mapInstr φ a) (mapInstr φ b) := rfl

/-- Relabelling commutes with bound renaming: it touches only `op` nodes. -/
@[simp] theorem mapInstr_rename (φ : Φ → Ψ) (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    mapInstr φ (Tm.rename ρ t) = Tm.rename ρ (mapInstr φ t) := by
  induction t generalizing m with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb | let₂ _ _ iha ihb | pair _ _ iha ihb
  | iter _ _ iha ihb => simp [iha, ihb]
  | case _ _ _ ihe ihl ihr => simp [ihe, ihl, ihr]

@[simp] theorem mapInstr_lift (φ : Φ → Ψ) (t : Tm ν Φ n) :
    mapInstr φ t.lift = (mapInstr φ t).lift := mapInstr_rename φ _ t

@[simp] theorem mapInstr_underBinder (φ : Φ → Ψ) (t : Tm ν Φ (n + 1)) :
    mapInstr φ t.underBinder = (mapInstr φ t).underBinder :=
  mapInstr_rename φ _ t

@[simp] theorem mapInstr_underTwoBinders (φ : Φ → Ψ) (t : Tm ν Φ (n + 2)) :
    mapInstr φ t.underTwoBinders = (mapInstr φ t).underTwoBinders :=
  mapInstr_rename φ _ t

/-- Relabelling a lifted substitution. -/
theorem mapInstr_upSub (φ : Φ → Ψ) (σ : Fin n → Tm ν Φ m) :
    (fun i => Tm.mapInstr φ (Syntax.upSub σ i)) =
      Syntax.upSub (fun i => Tm.mapInstr φ (σ i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp

/-- Relabelling commutes with simultaneous substitution. -/
theorem mapInstr_bsubst (φ : Φ → Ψ) :
    ∀ {n m : Nat} (σ : Fin n → Tm ν Φ m) (t : Tm ν Φ n),
      mapInstr φ (Tm.bsubst σ t) =
        Tm.bsubst (fun i => mapInstr φ (σ i)) (mapInstr φ t) := by
  intro n m σ t
  induction t generalizing m with
  | fv | bv | unit => rfl
  | op _ _ ih => simp [ih σ]
  | inl _ ih | inr _ ih | abort _ ih => simp [ih σ]
  | pair _ _ iha ihb => simp [iha σ, ihb σ]
  | let₁ _ _ iha ihb =>
      simp only [Syntax.bsubst_let₁, mapInstr_let₁, iha σ,
        ihb (Syntax.upSub σ), mapInstr_upSub]
  | iter _ _ iha ihb =>
      simp only [Syntax.bsubst_iter, mapInstr_iter, iha σ,
        ihb (Syntax.upSub σ), mapInstr_upSub]
  | let₂ _ _ iha ihb =>
      simp only [Syntax.bsubst_let₂, mapInstr_let₂, iha σ,
        ihb (Syntax.upSub (Syntax.upSub σ)), mapInstr_upSub]
  | case _ _ _ ihe ihl ihr =>
      simp only [Syntax.bsubst_case, mapInstr_case, ihe σ,
        ihl (Syntax.upSub σ), ihr (Syntax.upSub σ), mapInstr_upSub]

/-- Relabelling commutes with opening the newest binder. -/
@[simp] theorem mapInstr_instantiate (φ : Φ → Ψ) (b : Tm ν Φ (n + 1))
    (a : Tm ν Φ n) :
    mapInstr φ (Tm.instantiate b a) =
      Tm.instantiate (mapInstr φ b) (mapInstr φ a) := by
  rw [Tm.instantiate, mapInstr_bsubst, Tm.instantiate]
  exact Syntax.bsubst_congr (fun i => by refine Fin.cases rfl (fun j => rfl) i) _

end Tm

section Theory

variable {ε : Type u} {ε' : Type v} [HasEff Φ ε] [HasEff Ψ ε']
  {pureEff : ε} {pureEff' : ε'}

/-- Syntactic purity transports along any instruction relabelling that
preserves purity. -/
theorem Pure.mapInstr {φ : Φ → Ψ}
    (hφ : ∀ f : Φ, IsPure pureEff f → IsPure pureEff' (φ f)) :
    ∀ {n : Nat} {a : Tm ν Φ n},
      Pure pureEff a → Pure pureEff' (Tm.mapInstr φ a)
  | _, _, .fv => .fv
  | _, _, .bv => .bv
  | _, _, .op hf h => .op (hφ _ hf) (Pure.mapInstr hφ h)
  | _, _, .let₁ ha hb => .let₁ (Pure.mapInstr hφ ha) (Pure.mapInstr hφ hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (Pure.mapInstr hφ ha) (Pure.mapInstr hφ hb)
  | _, _, .let₂ ha hb => .let₂ (Pure.mapInstr hφ ha) (Pure.mapInstr hφ hb)
  | _, _, .inl h => .inl (Pure.mapInstr hφ h)
  | _, _, .inr h => .inr (Pure.mapInstr hφ h)
  | _, _, .case he hl hr =>
      .case (Pure.mapInstr hφ he) (Pure.mapInstr hφ hl) (Pure.mapInstr hφ hr)
  | _, _, .abort h => .abort (Pure.mapInstr hφ h)

/-- Structural axioms transport along a purity-preserving relabelling. -/
theorem StructuralAxiom.mapInstr {φ : Φ → Ψ}
    (hφ : ∀ f : Φ, IsPure pureEff f → IsPure pureEff' (φ f)) :
    ∀ {n : Nat} {a b : Tm ν Φ n}, StructuralAxiom pureEff a b →
      StructuralAxiom pureEff' (Tm.mapInstr φ a) (Tm.mapInstr φ b)
  | _, _, _, .letBeta hp => by
      simpa using StructuralAxiom.letBeta (hp.mapInstr hφ)
  | _, _, _, .letEta _ => .letEta _
  | _, _, _, .unitEta _ => .unitEta _
  | _, _, _, .pairBeta _ _ _ => by
      simpa using StructuralAxiom.pairBeta (pureEff := pureEff')
        (Tm.mapInstr φ _) (Tm.mapInstr φ _) (Tm.mapInstr φ _)
  | _, _, _, .pairEta _ => .pairEta _
  | _, _, _, .caseBetaL _ _ _ => .caseBetaL _ _ _
  | _, _, _, .caseBetaR _ _ _ => .caseBetaR _ _ _
  | _, _, _, .caseEta _ => .caseEta _
  | _, _, _, .emptyInitial _ _ _ => .emptyInitial _ _ _

/-- Sequencing axioms transport along any relabelling. -/
theorem SequencingAxiom.mapInstr (φ : Φ → Ψ) :
    ∀ {n : Nat} {a b : Tm ν Φ n}, SequencingAxiom pureEff a b →
      SequencingAxiom pureEff' (Tm.mapInstr φ a) (Tm.mapInstr φ b)
  | _, _, _, .bindOp _ _ => by
      simpa using SequencingAxiom.bindOp (pureEff := pureEff') (f := φ _)
        (Tm.mapInstr φ _) (Tm.mapInstr φ _)
  | _, _, _, .bindLet _ _ _ => by
      simpa using SequencingAxiom.bindLet (pureEff := pureEff')
        (Tm.mapInstr φ _) (Tm.mapInstr φ _) (Tm.mapInstr φ _)
  | _, _, _, .bindLetPair _ _ _ => by
      simpa using SequencingAxiom.bindLetPair (pureEff := pureEff')
        (Tm.mapInstr φ _) (Tm.mapInstr φ _) (Tm.mapInstr φ _)
  | _, _, _, .bindLetCase _ _ _ _ => by
      simpa using SequencingAxiom.bindLetCase (pureEff := pureEff')
        (Tm.mapInstr φ _) (Tm.mapInstr φ _) (Tm.mapInstr φ _) (Tm.mapInstr φ _)
  | _, _, _, .bindPair _ _ => by
      simpa using SequencingAxiom.bindPair (pureEff := pureEff')
        (Tm.mapInstr φ _) (Tm.mapInstr φ _)
  | _, _, _, .bindCase _ _ _ => by
      simpa using SequencingAxiom.bindCase (pureEff := pureEff')
        (Tm.mapInstr φ _) (Tm.mapInstr φ _) (Tm.mapInstr φ _)

/-- Iteration axioms transport along any relabelling. -/
theorem IterationAxiom.mapInstr (φ : Φ → Ψ) :
    ∀ {n : Nat} {a b : Tm ν Φ n}, IterationAxiom pureEff a b →
      IterationAxiom pureEff' (Tm.mapInstr φ a) (Tm.mapInstr φ b)
  | _, _, _, .fixpoint _ _ => by
      simpa using IterationAxiom.fixpoint (pureEff := pureEff')
        (Tm.mapInstr φ _) (Tm.mapInstr φ _)
  | _, _, _, .naturality _ _ _ => by
      simpa using IterationAxiom.naturality (pureEff := pureEff')
        (Tm.mapInstr φ _) (Tm.mapInstr φ _) (Tm.mapInstr φ _)
  | _, _, _, .codiagonal _ _ => by
      simpa using IterationAxiom.codiagonal (pureEff := pureEff')
        (Tm.mapInstr φ _) (Tm.mapInstr φ _)
  | _, _, _, .iterBind _ _ => by
      simpa using IterationAxiom.iterBind (pureEff := pureEff')
        (Tm.mapInstr φ _) (Tm.mapInstr φ _)

/-- Every raw axiom transports along a purity-preserving relabelling. -/
theorem CoreAxiom.mapInstr {φ : Φ → Ψ}
    (hφ : ∀ f : Φ, IsPure pureEff f → IsPure pureEff' (φ f)) :
    ∀ {n : Nat} {a b : Tm ν Φ n}, CoreAxiom pureEff a b →
      CoreAxiom pureEff' (Tm.mapInstr φ a) (Tm.mapInstr φ b)
  | _, _, _, .structural h => .structural (h.mapInstr hφ)
  | _, _, _, .sequencing h => .sequencing (h.mapInstr φ)
  | _, _, _, .iteration h => .iteration (h.mapInstr φ)

end Theory

end Isotope.LambdaIter.LocallyNameless
