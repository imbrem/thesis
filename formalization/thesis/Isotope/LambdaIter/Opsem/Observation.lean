import Isotope.LambdaIter.Opsem.Adequacy

/-!
# Observational equivalence, and the soundness half of the thesis claim

A *state model* (`Isotope.LambdaIter.Opsem.StateModel`) is one possible reading
of the individual operations of `λ_iter`: an abstract state set `S` together
with a total, deterministic transformer `run f : S → ⟦src f⟧ → S × ⟦trg f⟧` for
each instruction, subject only to the purity law that a `⊥`-effect instruction
neither reads nor writes the state.  Nothing else about `S` is assumed.

Two well-typed terms are *observationally equivalent*, `Observation.ObsEq`, when
they have the same operational outcome — the same terminating executions and the
same divergences — **in every state model at once**: for every state set, every
interpretation of the instructions on it, every environment, and every initial
state.  This is the relation the thesis' question is about.  The equational
theory is sound for it (`obsEq_of_related` below); it is *not* complete for it,
which is the business of the counterexample development.

## Why environments, and not closing syntactic contexts

The usual definition of observational equivalence quantifies over *program
contexts*: `a ≈ b` when `C[a]` and `C[b]` are indistinguishable for every closing
context `C`.  That definition is wrong here, and not merely inconvenient.

The signature `Φ` is a parameter of the language, and nothing forces it to
generate closed terms.  Over a signature whose every instruction has a base type
as its source — indeed over the empty signature — there is no closed term of a
base type `X` at all, so no context closes a variable of type `X`.  A
context-based observation would then relate *every* pair of open terms of type
`X` vacuously, and the completeness question would be a triviality about the
absence of closing contexts rather than a statement about the equational theory.

Quantifying over *semantic* environments `γ : CtxDen Γ`, `ρ : BoundDen β`
instead removes that accident: the environment supplies an arbitrary element of
`⟦X⟧` for each free variable whether or not any term denotes it.  It is also the
right notion for the comparison with the denotational semantics, which is itself
a function of a derivation and a pair of environments, and it is strictly
stronger than the context-based reading whenever both are non-vacuous, since a
closing context induces an environment.

## Why the quantification over state models is outside

`ObsEq` quantifies over state models *outside* the environments and the initial
state, so a distinguishing observation may be witnessed by any state model
whatsoever.  Equivalently — this is `obsEq_iff_denote` — `ObsEq` is equality of
denotations in `StateT S Part` for every `S`.  So a proof of `ObsEq` must handle
every possible meaning of the instructions, while a refutation need only exhibit
one state model, one environment and one state.
-/

namespace Isotope.LambdaIter.Opsem

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

namespace Observation

/-! ## The definition -/

/-- Agreement of the two `Diverges` predicates follows from agreement of the two
`Eval` relations, since divergence is the absence of an evaluation. -/
theorem diverges_congr {S : Type v} [StateModel Φ τ ε S]
    {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s : S}
    (hE : ∀ (s' : S) (v : TyDen A),
      Eval (ε := ε) ha γ ρ s s' v ↔ Eval (ε := ε) hb γ ρ s s' v) :
    Diverges (ε := ε) ha γ ρ s ↔ Diverges (ε := ε) hb γ ρ s := by
  constructor
  · rintro hd ⟨s', v, hv⟩
    exact hd ⟨s', v, (hE s' v).2 hv⟩
  · rintro hd ⟨s', v, hv⟩
    exact hd ⟨s', v, (hE s' v).1 hv⟩

/-- **Observational equivalence.**  Two typing derivations at the same context,
bound context and type are observationally equivalent when, in *every* state
model — every state set `S` in the interpretation universe `v` fixed by
`TypeModel.{u, v} τ`, and every `StateModel` structure on it — under every pair
of environments and from every initial state, they have exactly the same
terminating executions and diverge in exactly the same circumstances.

The quantification is over semantic environments rather than over closing
syntactic contexts; see the module docstring for why the latter would make the
statement vacuous over signatures with few closed terms.

The `Diverges` conjunct is implied by the `Eval` conjunct (`diverges_congr`); it
is spelled out because it is half of what "same operational outcome" means. -/
def ObsEq {a b : Tm ν Φ n} {A : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) : Prop :=
  ∀ (S : Type v) [StateModel Φ τ ε S] (γ : CtxDen Γ) (ρ : BoundDen β) (s : S),
    (∀ (s' : S) (v : TyDen A),
        Eval (ε := ε) ha γ ρ s s' v ↔ Eval (ε := ε) hb γ ρ s s' v) ∧
      (Diverges (ε := ε) ha γ ρ s ↔ Diverges (ε := ε) hb γ ρ s)

variable {a b c : Tm ν Φ n} {A : τ}
  {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A} {hc : HasType Φ Γ β c A}

/-- Observationally equivalent derivations have the same terminating
executions. -/
theorem ObsEq.eval_iff (h : ObsEq (ε := ε) ha hb) (S : Type v)
    [StateModel Φ τ ε S] (γ : CtxDen Γ) (ρ : BoundDen β) (s s' : S)
    (v : TyDen A) :
    Eval (ε := ε) ha γ ρ s s' v ↔ Eval (ε := ε) hb γ ρ s s' v :=
  (h S γ ρ s).1 s' v

/-- Observationally equivalent derivations diverge in the same
circumstances. -/
theorem ObsEq.diverges_iff (h : ObsEq (ε := ε) ha hb) (S : Type v)
    [StateModel Φ τ ε S] (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    Diverges (ε := ε) ha γ ρ s ↔ Diverges (ε := ε) hb γ ρ s :=
  (h S γ ρ s).2

/-- Agreement of the evaluation relations already gives observational
equivalence. -/
theorem obsEq_of_eval_iff
    (hE : ∀ (S : Type v) [StateModel Φ τ ε S] (γ : CtxDen Γ) (ρ : BoundDen β)
      (s s' : S) (v : TyDen A),
      Eval (ε := ε) ha γ ρ s s' v ↔ Eval (ε := ε) hb γ ρ s s' v) :
    ObsEq (ε := ε) ha hb := by
  intro S _ γ ρ s
  exact ⟨fun s' v => hE S γ ρ s s' v, diverges_congr fun s' v => hE S γ ρ s s' v⟩

/-! ## Observational equivalence is an equivalence relation -/

/-- Observational equivalence is reflexive. -/
@[refl] theorem ObsEq.refl (ha : HasType Φ Γ β a A) : ObsEq (ε := ε) ha ha := by
  intro S _ γ ρ s
  exact ⟨fun _ _ => Iff.rfl, Iff.rfl⟩

/-- Observational equivalence is symmetric. -/
theorem ObsEq.symm (h : ObsEq (ε := ε) ha hb) : ObsEq (ε := ε) hb ha := by
  intro S _ γ ρ s
  exact ⟨fun s' v => ((h S γ ρ s).1 s' v).symm, (h S γ ρ s).2.symm⟩

/-- Observational equivalence is transitive. -/
theorem ObsEq.trans (h : ObsEq (ε := ε) ha hb) (k : ObsEq (ε := ε) hb hc) :
    ObsEq (ε := ε) ha hc := by
  intro S _ γ ρ s
  exact ⟨fun s' v => ((h S γ ρ s).1 s' v).trans ((k S γ ρ s).1 s' v),
    (h S γ ρ s).2.trans (k S γ ρ s).2⟩

/-- A well-typed term at a fixed context, bound context and type: the carrier on
which observational equivalence is an honest equivalence relation. -/
def Typed (Φ : Type q) [HasTy Φ τ] (Γ : Ctx ν τ) (β : BoundCtx τ n) (A : τ) :
    Type (max u q w) :=
  Σ t : Tm ν Φ n, HasType Φ Γ β t A

/-- Observational equivalence, as a relation on `Typed`. -/
def ObsEqOn (ε : Type r) [HasEff Φ ε] [Bot ε]
    (x y : Typed (τ := τ) Φ Γ β A) : Prop :=
  ObsEq (ε := ε) x.2 y.2

/-- Observational equivalence is an equivalence relation. -/
theorem obsEqOn_equivalence :
    Equivalence (ObsEqOn (τ := τ) (Φ := Φ) (Γ := Γ) (β := β) (A := A) ε) where
  refl x := ObsEq.refl x.2
  symm h := ObsEq.symm h
  trans h k := ObsEq.trans h k

/-! ## The bridge to the denotational semantics -/

/-- **Observational equivalence is denotational equality in `StateT S Part`,
uniformly in the state model.**  This is what makes `ObsEq` usable: an
operational statement quantified over all state models is exactly a
denotational one, by adequacy (`eval_iff_denote`, `diverges_iff_denote_none`). -/
theorem obsEq_iff_denote (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
    ObsEq (ε := ε) ha hb ↔
      ∀ (S : Type v) [StateModel Φ τ ε S] (γ : CtxDen Γ) (ρ : BoundDen β),
        denote (m := Elgot.PartState S) (ε := ε) ha γ ρ =
          denote (m := Elgot.PartState S) (ε := ε) hb γ ρ := by
  constructor
  · intro h S _ γ ρ
    funext s
    apply Part.ext
    intro z
    exact ((eval_iff_denote ha γ ρ s z.2 z.1).symm.trans
      ((h S γ ρ s).1 z.2 z.1)).trans (eval_iff_denote hb γ ρ s z.2 z.1)
  · intro hd
    refine obsEq_of_eval_iff (ε := ε) ?_
    intro S _ γ ρ s s' v
    rw [eval_iff_denote ha γ ρ s s' v, eval_iff_denote hb γ ρ s s' v, hd S γ ρ]

/-- Observational equivalence follows from denotational equality in every
`StateT S Part`. -/
theorem obsEq_of_denote_eq
    (hd : ∀ (S : Type v) [StateModel Φ τ ε S] (γ : CtxDen Γ) (ρ : BoundDen β),
      denote (m := Elgot.PartState S) (ε := ε) ha γ ρ =
        denote (m := Elgot.PartState S) (ε := ε) hb γ ρ) :
    ObsEq (ε := ε) ha hb :=
  (obsEq_iff_denote ha hb).2 hd

/-! ## Soundness: the equational theory is observationally sound -/

/-- **Soundness.**  Two derivations related by the proof-relevant typed
equational theory are observationally equivalent: they cannot be told apart by
any state model, any environment, or any initial state.

The proof is `Isotope.LambdaIter.Subtyping.Semantics.related_sound` at
`m := StateT S Part` — legitimate because `Isotope.Elgot.StateT.instIterate` and
`Isotope.Elgot.StateT.instLawfulElgotMonad` make partial state transformers a
lawful Elgot monad, and `instructionModelOfStateModel` turns the state model
into an instruction model for it — followed by adequacy. -/
theorem obsEq_of_related (h : TypedEquiv.Related (⊥ : ε) Γ ha hb) :
    ObsEq (ε := ε) ha hb :=
  (obsEq_iff_denote ha hb).2 fun S _ γ ρ =>
    Subtyping.Semantics.related_sound (m := Elgot.PartState S) (ε := ε) h γ ρ

/-- **Soundness**, taking the derivation itself rather than its truncation. -/
theorem obsEq_of_deriv (d : TypedEquiv.Deriv (⊥ : ε) Γ ha hb) :
    ObsEq (ε := ε) ha hb :=
  obsEq_of_related ⟨d⟩

/-! ## Relation to the single-model, closed-term observation -/

/-- Observational equivalence implies the single-model observation of
`Isotope.LambdaIter.Opsem.ModelObsEq` for closed programs: equality of the
`Part`-valued outcome from every state, in the given state model. -/
theorem ObsEq.toModelObsEq {t₁ t₂ : Tm Empty Φ 0} {A : τ}
    {h₁ : HasType Φ (.nil : Ctx Empty τ) .nil t₁ A}
    {h₂ : HasType Φ (.nil : Ctx Empty τ) .nil t₂ A}
    (h : ObsEq (ε := ε) h₁ h₂) (S : Type v) [StateModel Φ τ ε S] :
    Isotope.LambdaIter.Opsem.ModelObsEq (ε := ε) (S := S) h₁ h₂ := by
  intro s
  apply Part.ext
  intro z
  rw [observeClosed_eq, observeClosed_eq, mem_observe_iff, mem_observe_iff]
  exact (h S PUnit.unit PUnit.unit s).1 z.1 z.2

end Observation

end Isotope.LambdaIter.Opsem
