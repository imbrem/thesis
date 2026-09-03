import Isotope.LambdaIter.Semantics.Kleisli.Coherence
import Isotope.LambdaIter.Subtyping.Semantics.Soundness
import Isotope.LambdaIter.Models.Monadic.Alg

/-!
# Soundness of the raw axiom schemes for the coercion-free denotation

Every scheme of `LambdaIter.CoreAxiom` is discharged for the set-valued
coercion-free denotation, at an arbitrary free context.  Nothing is reproved:
each case invokes the corresponding lemma of
`Isotope/LambdaIter/Subtyping/Semantics/Soundness.lean` through the embedding
`HasType.toGeneric`, which is legitimate because the canonical *subtyping*
derivations those lemmas build out of embedded derivations are themselves
embeddings of the canonical *exact* derivations
(`Isotope/LambdaIter/Semantics/Kleisli/Generic.lean`).

What is genuinely new here is the inversion glue: `Eqv.ax` carries a raw axiom
together with two arbitrary endpoint derivations, so each case must invert one
endpoint, rebuild the other canonically, and bridge the two by coherence.
-/

namespace Isotope.LambdaIter.Semantics

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless
open Isotope.Elgot

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m]
variable [InstructionModel Φ τ ε m]
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

section Structural

/-- Beta for a pure `let`. -/
theorem sound_letBeta {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (hp : Pure (⊥ : ε) a) (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b B) (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₁ ha hb) γ ρ =
      exactDenote (ε := ε) (m := m) (hb.instantiate ha) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_let₁,
    HasType.toGeneric_instantiate] using
    Subtyping.Semantics.sound_letBeta (m := m) (ε := ε) hp.toGeneric ha.toGeneric
      hb.toGeneric γ ρ

/-- Eta for `let`. -/
theorem sound_letEta {a : Tm ν Φ n} {A : τ} (ha : HasType Φ Γ β a A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₁ ha HasType.newest) γ ρ =
      exactDenote (ε := ε) (m := m) ha γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_let₁,
    HasType.toGeneric_newest] using
    Subtyping.Semantics.sound_letEta (m := m) (ε := ε) ha.toGeneric γ ρ

/-- Eta for the unit type. -/
theorem sound_unitEta {a : Tm ν Φ n}
    (ha : HasType Φ Γ β a (TypeFormers.unit : τ))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₁ ha .unit) γ ρ =
      exactDenote (ε := ε) (m := m) ha γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_let₁,
    HasType.toGeneric_unit] using
    Subtyping.Semantics.sound_unitEta (m := m) (ε := ε) ha.toGeneric γ ρ

/-- Eta for the tensor. -/
theorem sound_pairEta {a : Tm ν Φ n} {A B : τ}
    (ha : HasType Φ Γ β a (TypeFormers.tensor A B))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m)
        (.let₂ ha (.pair HasType.previous HasType.newest)) γ ρ =
      exactDenote (ε := ε) (m := m) ha γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_let₂, HasType.toGeneric_pair,
    HasType.toGeneric_newest, HasType.toGeneric_previous] using
    Subtyping.Semantics.sound_pairEta (m := m) (ε := ε) ha.toGeneric γ ρ

/-- Eta for the coproduct. -/
theorem sound_caseEta {e : Tm ν Φ n} {A B : τ}
    (he : HasType Φ Γ β e (TypeFormers.coprod A B))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m)
        (.case he (.inl HasType.newest) (.inr HasType.newest)) γ ρ =
      exactDenote (ε := ε) (m := m) he γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_case, HasType.toGeneric_inl,
    HasType.toGeneric_inr, HasType.toGeneric_newest] using
    Subtyping.Semantics.sound_caseEta (m := m) (ε := ε) he.toGeneric γ ρ

/-- Beta for the tensor. -/
theorem sound_pairBeta {a b : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
    (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₂ (.pair ha hb) hc) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.let₁ ha (.let₁ (hb.lift (B := A)) hc)) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_let₂, HasType.toGeneric_pair,
    HasType.toGeneric_let₁, HasType.toGeneric_lift] using
    Subtyping.Semantics.sound_pairBeta (m := m) (ε := ε) ha.toGeneric
      hb.toGeneric hc.toGeneric γ ρ

/-- Beta for the left injection. -/
theorem sound_caseBetaL {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
    (he : HasType Φ Γ β e A) (hl : HasType Φ Γ (.snoc β A) l C)
    (hr : HasType Φ Γ (.snoc β B) r C) (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.case (.inl he) hl hr) γ ρ =
      exactDenote (ε := ε) (m := m) (.let₁ he hl) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_case, HasType.toGeneric_inl,
    HasType.toGeneric_let₁] using
    Subtyping.Semantics.sound_caseBetaL (m := m) (ε := ε) he.toGeneric
      hl.toGeneric hr.toGeneric γ ρ

/-- Beta for the right injection. -/
theorem sound_caseBetaR {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
    (he : HasType Φ Γ β e B) (hl : HasType Φ Γ (.snoc β A) l C)
    (hr : HasType Φ Γ (.snoc β B) r C) (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.case (.inr he) hl hr) γ ρ =
      exactDenote (ε := ε) (m := m) (.let₁ he hr) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_case, HasType.toGeneric_inr,
    HasType.toGeneric_let₁] using
    Subtyping.Semantics.sound_caseBetaR (m := m) (ε := ε) he.toGeneric
      hl.toGeneric hr.toGeneric γ ρ

end Structural

section Sequencing

/-- Sequencing an instruction. -/
theorem sound_bindOp {a : Tm ν Φ n} {c : Tm ν Φ (n + 1)} {C : τ} {f : Φ}
    (ha : HasType Φ Γ β a (instrSrc f))
    (hc : HasType Φ Γ (.snoc β (instrTrg f)) c C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₁ (.op ha) hc) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.let₁ ha (.let₁ (.op HasType.newest) hc.underBinder)) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_let₁, HasType.toGeneric_op,
    HasType.toGeneric_newest, HasType.toGeneric_underBinder] using
    Subtyping.Semantics.sound_bindOp (m := m) (ε := ε) ha.toGeneric
      hc.toGeneric γ ρ

/-- Sequencing a `let`. -/
theorem sound_bindLet {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A B C : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B)
    (hc : HasType Φ Γ (.snoc β B) c C) (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₁ (.let₁ ha hb) hc) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.let₁ ha (.let₁ hb hc.underBinder)) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_let₁,
    HasType.toGeneric_underBinder] using
    Subtyping.Semantics.sound_bindLet (m := m) (ε := ε) ha.toGeneric
      hb.toGeneric hc.toGeneric γ ρ

/-- Sequencing a pair elimination. -/
theorem sound_bindLetPair {e : Tm ν Φ n} {c : Tm ν Φ (n + 2)}
    {d : Tm ν Φ (n + 1)} {A B C D : τ}
    (he : HasType Φ Γ β e (TypeFormers.tensor A B))
    (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
    (hd : HasType Φ Γ (.snoc β C) d D) (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₁ (.let₂ he hc) hd) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.let₂ he (.let₁ hc (hd.underBinder.underBinder))) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_let₁, HasType.toGeneric_let₂,
    HasType.toGeneric_underBinder] using
    Subtyping.Semantics.sound_bindLetPair (m := m) (ε := ε) he.toGeneric
      hc.toGeneric hd.toGeneric γ ρ

/-- Sequencing a case. -/
theorem sound_bindLetCase {e : Tm ν Φ n} {l r d : Tm ν Φ (n + 1)}
    {A B C D : τ} (he : HasType Φ Γ β e (TypeFormers.coprod A B))
    (hl : HasType Φ Γ (.snoc β A) l C) (hr : HasType Φ Γ (.snoc β B) r C)
    (hd : HasType Φ Γ (.snoc β C) d D) (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₁ (.case he hl hr) hd) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.case he (.let₁ hl hd.underBinder) (.let₁ hr hd.underBinder)) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_let₁, HasType.toGeneric_case,
    HasType.toGeneric_underBinder] using
    Subtyping.Semantics.sound_bindLetCase (m := m) (ε := ε) he.toGeneric
      hl.toGeneric hr.toGeneric hd.toGeneric γ ρ

/-- Naming the scrutinee of a pair elimination. -/
theorem sound_bindPair {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
    (ha : HasType Φ Γ β a (TypeFormers.tensor A B))
    (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₂ ha hc) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.let₁ ha (.let₂ HasType.newest hc.underTwoBinders)) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_let₂, HasType.toGeneric_let₁,
    HasType.toGeneric_newest, HasType.toGeneric_underTwoBinders] using
    Subtyping.Semantics.sound_bindPair (m := m) (ε := ε) ha.toGeneric
      hc.toGeneric γ ρ

/-- Naming the scrutinee of a case. -/
theorem sound_bindCase {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
    (he : HasType Φ Γ β e (TypeFormers.coprod A B))
    (hl : HasType Φ Γ (.snoc β A) l C) (hr : HasType Φ Γ (.snoc β B) r C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.case he hl hr) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.let₁ he (.case HasType.newest hl.underBinder hr.underBinder)) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_case, HasType.toGeneric_let₁,
    HasType.toGeneric_newest, HasType.toGeneric_underBinder] using
    Subtyping.Semantics.sound_bindCase (m := m) (ε := ε) he.toGeneric
      hl.toGeneric hr.toGeneric γ ρ

end Sequencing

section Iteration

variable [LawfulElgotMonad m]

/-- Naming the seed of a loop. -/
theorem sound_iterBind {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.iter ha hb) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.let₁ ha (.iter HasType.newest hb.underBinder)) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_iter, HasType.toGeneric_let₁,
    HasType.toGeneric_newest, HasType.toGeneric_underBinder] using
    Subtyping.Semantics.sound_iterBind (m := m) (ε := ε) ha.toGeneric
      hb.toGeneric γ ρ

/-- The Elgot fixpoint law. -/
theorem sound_iterFixpoint {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.iter ha hb) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.let₁ ha (.case hb HasType.newest
          (.iter HasType.newest hb.underBinder.underBinder))) γ ρ := by
  simpa only [exactDenote, HasType.toGeneric_iter, HasType.toGeneric_let₁,
    HasType.toGeneric_case, HasType.toGeneric_newest,
    HasType.toGeneric_underBinder] using
    Subtyping.Semantics.sound_iterFixpoint (m := m) (ε := ε) ha.toGeneric
      hb.toGeneric γ ρ

/-- The Elgot naturality law. -/
theorem sound_iterNaturality {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A B C : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A))
    (hc : HasType Φ Γ (.snoc β B) c C) (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₁ (.iter ha hb) hc) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.iter ha (.case hb (.inl hc.underBinder) (.inr HasType.newest)))
          γ ρ := by
  have e : (HasType.iter ha (HasType.case hb (.inl hc.underBinder)
        (.inr HasType.newest))).toGeneric =
      Subtyping.LocallyNameless.HasType.iter ha.toGeneric
        (.case hb.toGeneric (.inl hc.toGeneric.underBinder)
          (.inr Subtyping.LocallyNameless.HasType.newest)) := by
    show Subtyping.LocallyNameless.HasType.iter _
      (Subtyping.LocallyNameless.HasType.case _ (.inl _) (.inr _)) = _
    rw [HasType.toGeneric_underBinder hc]
    rfl
  simp only [exactDenote, e, HasType.toGeneric_let₁, HasType.toGeneric_iter]
  exact Subtyping.Semantics.sound_iterNaturality (m := m) (ε := ε) ha.toGeneric
    hb.toGeneric hc.toGeneric γ ρ

/-- The Elgot codiagonal law. -/
theorem sound_iterCodiagonal {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b
      (TypeFormers.coprod (TypeFormers.coprod B A) A))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m)
        (.iter ha (.iter HasType.newest hb.underBinder)) γ ρ =
      exactDenote (ε := ε) (m := m)
        (.iter ha (.case hb HasType.newest (.inr HasType.newest))) γ ρ := by
  have e : (HasType.iter ha
        (HasType.iter HasType.newest hb.underBinder)).toGeneric =
      Subtyping.LocallyNameless.HasType.iter ha.toGeneric
        (.iter Subtyping.LocallyNameless.HasType.newest
          hb.toGeneric.underBinder) := by
    exact congrArg (Subtyping.LocallyNameless.HasType.iter ha.toGeneric)
      (congrArg (Subtyping.LocallyNameless.HasType.iter
        Subtyping.LocallyNameless.HasType.newest)
        (HasType.toGeneric_underBinder hb))
  simp only [exactDenote, e, HasType.toGeneric_iter, HasType.toGeneric_case,
    HasType.toGeneric_inr, HasType.toGeneric_newest]
  exact Subtyping.Semantics.sound_iterCodiagonal (m := m) (ε := ε) ha.toGeneric
    hb.toGeneric γ ρ

/-- The Elgot uniformity rule, with its commuting square supplied
semantically. -/
theorem sound_iterUniformity {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)}
    {A A' B : τ} (ha : HasType Φ Γ β a A)
    (hh : HasType Φ Γ (.snoc β A) h A') (hp : Pure (⊥ : ε) h)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A))
    (hb' : HasType Φ Γ (.snoc β A') b' (TypeFormers.coprod B A'))
    (hsquare : ∀ (γ : CtxDen Γ) (ρA : BoundDen (BoundCtx.snoc β A)),
      exactDenote (ε := ε) (m := m)
          (.case hb (.inl HasType.newest) (.inr hh.underBinder)) γ ρA =
        exactDenote (ε := ε) (m := m) ((hb'.underBinder).instantiate hh) γ ρA)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.iter ha hb) γ ρ =
      exactDenote (ε := ε) (m := m) (.iter (.let₁ ha hh) hb') γ ρ := by
  have hsq : ∀ (γ' : CtxDen Γ) (ρA : BoundDen (BoundCtx.snoc β A)),
      Subtyping.Semantics.denote (m := m) (ε := ε)
          (.case hb.toGeneric
            (.inl Subtyping.LocallyNameless.HasType.newest)
            (.inr hh.toGeneric.underBinder)) γ' ρA =
        Subtyping.Semantics.denote (m := m) (ε := ε)
          ((hb'.toGeneric.underBinder).instantiate hh.toGeneric) γ' ρA := by
    intro γ' ρA
    have hx := hsquare γ' ρA
    simp only [exactDenote, HasType.toGeneric_case, HasType.toGeneric_inl,
      HasType.toGeneric_inr, HasType.toGeneric_newest,
      HasType.toGeneric_underBinder, HasType.toGeneric_instantiate] at hx
    exact hx
  simpa only [exactDenote, HasType.toGeneric_iter, HasType.toGeneric_let₁]
    using Subtyping.Semantics.sound_iterUniformity (m := m) (ε := ε)
      ha.toGeneric hh.toGeneric hp.toGeneric hb.toGeneric hb'.toGeneric hsq γ ρ

end Iteration


section Axioms

variable [LawfulElgotMonad m] [InjectiveFormers τ]

/-- Eta for the unit type, across types.  The discarded scrutinee may be typed
at anything on the left, so the two sides have sub-derivations at genuinely
different types and the coupling is needed. -/
theorem sound_unitEtaAcross {a : Tm ν Φ n} {A : τ}
    (h₁ : HasType Φ Γ β a A)
    (hu : HasType Φ Γ β a (TypeFormers.unit : τ))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₁ h₁ .unit) γ ρ =
      exactDenote (ε := ε) (m := m) hu γ ρ := by
  simp only [exactDenote_let₁, exactDenote_unit]
  rw [← bind_pure (exactDenote (ε := ε) (m := m) hu γ ρ)]
  refine Coupled.bind_eq
    (denote_coupled (ε := ε) h₁ hu γ ρ ρ (EnvRel.refl' ρ)) ?_
  intro p
  have hv : (TypeModel.unitEquiv.symm () : TyDen (TypeFormers.unit : τ)) =
      p.val.2 := TypeModel.unitEquiv.injective (Subsingleton.elim _ _)
  rw [hv]
  exact Coupled.refl' (τ := τ) _

/-- Two `abort` continuations agree, whatever their binder types and whatever
derivation the aborted subterm is given. -/
theorem sound_emptyInitial {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A A' B : τ}
    (hz hz' : HasType Φ Γ β a (TypeFormers.empty : τ))
    (hb : HasType Φ Γ (.snoc β A) b B) (hc : HasType Φ Γ (.snoc β A') c B)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (.let₁ (.abort hz) hb) γ ρ =
      exactDenote (ε := ε) (m := m) (.let₁ (.abort hz') hc) γ ρ := by
  simp only [exactDenote_let₁, exactDenote_abort]
  rw [exactDenote_coh (ε := ε) hz hz' γ ρ]
  simp only [LawfulMonad.bind_assoc]
  exact bind_congr fun z => (TypeModel.emptyEquiv z).elim

/-- **Soundness of the raw axiom schemes.**  Each case inverts the derivation
of one endpoint, builds a canonical derivation of the other, and appeals to the
corresponding lemma above; coherence bridges the given derivations and the
canonical ones. -/
theorem sound_ax {a b : Tm ν Φ n} {A : τ}
    (hax : CoreAxiom (⊥ : ε) a b)
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) ha γ ρ =
      exactDenote (ε := ε) (m := m) hb γ ρ := by
  cases hax with
  | structural hs =>
      cases hs with
      | letBeta hp =>
          cases ha with
          | let₁ h₁ h₂ =>
              exact (sound_letBeta hp h₁ h₂ γ ρ).trans
                (exactDenote_coh (ε := ε) (h₂.instantiate h₁) hb γ ρ)
      | letEta _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₂
              exact (exactDenote_coh (ε := ε) (.let₁ h₁ HasType.bv)
                  (.let₁ h₁ HasType.newest) γ ρ).trans
                ((sound_letEta h₁ γ ρ).trans
                  (exactDenote_coh (ε := ε) h₁ hb γ ρ))
      | unitEta _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₂
              exact sound_unitEtaAcross h₁ hb γ ρ
      | pairBeta _ _ _ =>
          cases ha with
          | let₂ h₁ h₂ =>
              obtain ⟨p₁, p₂⟩ := h₁.pair_inv rfl
              exact (exactDenote_coh (ε := ε) (.let₂ h₁ h₂)
                  (.let₂ (.pair p₁ p₂) h₂) γ ρ).trans
                ((sound_pairBeta p₁ p₂ h₂ γ ρ).trans
                  (exactDenote_coh (ε := ε) (.let₁ p₁ (.let₁ p₂.lift h₂))
                    hb γ ρ))
      | pairEta _ =>
          cases ha with
          | let₂ h₁ h₂ =>
              cases h₂ with
              | pair q₁ q₂ =>
                  cases q₁
                  cases q₂
                  exact (exactDenote_coh (ε := ε) (.let₂ h₁ (.pair .bv .bv))
                      (.let₂ h₁ (.pair HasType.previous HasType.newest))
                      γ ρ).trans
                    ((sound_pairEta h₁ γ ρ).trans
                      (exactDenote_coh (ε := ε) h₁ hb γ ρ))
      | caseBetaL _ _ _ =>
          cases ha with
          | case h₁ hl hr =>
              have he := h₁.inl_inv rfl
              exact (exactDenote_coh (ε := ε) (.case h₁ hl hr)
                  (.case (.inl he) hl hr) γ ρ).trans
                ((sound_caseBetaL he hl hr γ ρ).trans
                  (exactDenote_coh (ε := ε) (.let₁ he hl) hb γ ρ))
      | caseBetaR _ _ _ =>
          cases ha with
          | case h₁ hl hr =>
              have he := h₁.inr_inv rfl
              exact (exactDenote_coh (ε := ε) (.case h₁ hl hr)
                  (.case (.inr he) hl hr) γ ρ).trans
                ((sound_caseBetaR he hl hr γ ρ).trans
                  (exactDenote_coh (ε := ε) (.let₁ he hr) hb γ ρ))
      | caseEta _ =>
          cases ha with
          | case h₁ hl hr =>
              cases hl with
              | inl u =>
                  cases u
                  cases HasType.inr_inv hr rfl
                  exact (exactDenote_coh (ε := ε) (.case h₁ (.inl .bv) hr)
                      (.case h₁ (.inl HasType.newest) (.inr HasType.newest))
                      γ ρ).trans
                    ((sound_caseEta h₁ γ ρ).trans
                      (exactDenote_coh (ε := ε) h₁ hb γ ρ))
      | emptyInitial _ _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | abort hz =>
                  cases hb with
                  | let₁ k₁ k₂ =>
                      cases k₁ with
                      | abort hz' => exact sound_emptyInitial hz hz' h₂ k₂ γ ρ
  | sequencing hs =>
      cases hs with
      | bindOp _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | op haa =>
                  exact (sound_bindOp haa h₂ γ ρ).trans
                    (exactDenote_coh (ε := ε) _ hb γ ρ)
      | bindLet _ _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | let₁ g₁ g₂ =>
                  exact (sound_bindLet g₁ g₂ h₂ γ ρ).trans
                    (exactDenote_coh (ε := ε) _ hb γ ρ)
      | bindLetPair _ _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | let₂ g₁ g₂ =>
                  exact (sound_bindLetPair g₁ g₂ h₂ γ ρ).trans
                    (exactDenote_coh (ε := ε) _ hb γ ρ)
      | bindLetCase _ _ _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | case g₁ g₂ g₃ =>
                  exact (sound_bindLetCase g₁ g₂ g₃ h₂ γ ρ).trans
                    (exactDenote_coh (ε := ε) _ hb γ ρ)
      | bindPair _ _ =>
          cases ha with
          | let₂ h₁ h₂ =>
              exact (sound_bindPair h₁ h₂ γ ρ).trans
                (exactDenote_coh (ε := ε) _ hb γ ρ)
      | bindCase _ _ _ =>
          cases ha with
          | case h₁ hl hr =>
              exact (sound_bindCase h₁ hl hr γ ρ).trans
                (exactDenote_coh (ε := ε) _ hb γ ρ)
  | iteration hi =>
      cases hi with
      | fixpoint _ _ =>
          cases ha with
          | iter h₁ h₂ =>
              exact (sound_iterFixpoint h₁ h₂ γ ρ).trans
                (exactDenote_coh (ε := ε) _ hb γ ρ)
      | naturality _ _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | iter g₁ g₂ =>
                  exact (sound_iterNaturality g₁ g₂ h₂ γ ρ).trans
                    (exactDenote_coh (ε := ε) _ hb γ ρ)
      | codiagonal _ _ =>
          cases hb with
          | iter k₁ k₂ =>
              cases k₂ with
              | case c₁ c₂ c₃ =>
                  cases c₂
                  obtain rfl : _ = _ :=
                    HasType.bv_ty (HasType.inr_inv c₃ rfl)
                  exact (exactDenote_coh (ε := ε) ha
                      (.iter k₁ (.iter HasType.newest c₁.underBinder))
                      γ ρ).trans
                    ((sound_iterCodiagonal k₁ c₁ γ ρ).trans
                      (exactDenote_coh (ε := ε)
                        (.iter k₁ (.case c₁ HasType.newest
                          (.inr HasType.newest))) _ γ ρ))
      | iterBind _ _ =>
          cases ha with
          | iter h₁ h₂ =>
              exact (sound_iterBind h₁ h₂ γ ρ).trans
                (exactDenote_coh (ε := ε) _ hb γ ρ)

end Axioms

end Isotope.LambdaIter.Semantics
