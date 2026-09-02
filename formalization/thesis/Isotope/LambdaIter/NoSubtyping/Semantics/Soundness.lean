import Isotope.LambdaIter.NoSubtyping.Semantics.Categorical
import Isotope.LambdaIter.Semantics.IterationDiagrams

/-!
# Soundness infrastructure for coercion-free lambda-iter

The congruence closure is handled independently of the individual beta/eta,
sequencing, and Elgot calculations. This makes the remaining categorical
diagram proofs explicit in the `LawfulModel` boundary.
-/

namespace Isotope.LambdaIter.NoSubtyping.LocallyNameless

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅ u₆

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.Semantics

variable {τ : Type u₃} [TypeFormers τ] [Subtyping τ]
variable {ν : Type u₄} [DecidableEq ν]
variable {Φ : Type u₅} [HasTy Φ τ]
variable {ε : Type u₆} [HasEff Φ ε] {pureEff : ε}

namespace Eqv

/-- Both endpoints of a typed equation are typable. This proposition-valued
statement is eliminable from `Eqv`, which itself lives in `Prop`. -/
theorem typable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ} :
    Eqv (τ := τ) (ν := ν) (Φ := Φ) (ε := ε) pureEff Γ β a b A →
      Nonempty (HasType (τ := τ) (ν := ν) Φ Γ β a A) ∧
        Nonempty (HasType (τ := τ) (ν := ν) Φ Γ β b A) := by
  intro e
  induction e with
  | refl h => exact ⟨⟨h⟩, ⟨h⟩⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih ik => exact ⟨ih.1, ik.2⟩
  | op _ ih =>
      exact ⟨ih.1.map HasType.op, ih.2.map HasType.op⟩
  | let₁ _ _ iha ihb =>
      rcases iha with ⟨⟨ha⟩, ⟨ha'⟩⟩
      rcases ihb with ⟨⟨hb⟩, ⟨hb'⟩⟩
      exact ⟨⟨.let₁ ha hb⟩, ⟨.let₁ ha' hb'⟩⟩
  | unit => exact ⟨⟨.unit⟩, ⟨.unit⟩⟩
  | pair _ _ iha ihb =>
      rcases iha with ⟨⟨ha⟩, ⟨ha'⟩⟩
      rcases ihb with ⟨⟨hb⟩, ⟨hb'⟩⟩
      exact ⟨⟨.pair ha hb⟩, ⟨.pair ha' hb'⟩⟩
  | let₂ _ _ ihe ihc =>
      rcases ihe with ⟨⟨he⟩, ⟨he'⟩⟩
      rcases ihc with ⟨⟨hc⟩, ⟨hc'⟩⟩
      exact ⟨⟨.let₂ he hc⟩, ⟨.let₂ he' hc'⟩⟩
  | inl _ ih => exact ⟨ih.1.map HasType.inl, ih.2.map HasType.inl⟩
  | inr _ ih => exact ⟨ih.1.map HasType.inr, ih.2.map HasType.inr⟩
  | case _ _ _ ihe ihl ihr =>
      rcases ihe with ⟨⟨he⟩, ⟨he'⟩⟩
      rcases ihl with ⟨⟨hl⟩, ⟨hl'⟩⟩
      rcases ihr with ⟨⟨hr⟩, ⟨hr'⟩⟩
      exact ⟨⟨.case he hl hr⟩, ⟨.case he' hl' hr'⟩⟩
  | abort _ ih => exact ⟨ih.1.map HasType.abort, ih.2.map HasType.abort⟩
  | iter _ _ iha ihb =>
      rcases iha with ⟨⟨ha⟩, ⟨ha'⟩⟩
      rcases ihb with ⟨⟨hb⟩, ⟨hb'⟩⟩
      exact ⟨⟨.iter ha hb⟩, ⟨.iter ha' hb'⟩⟩
  | ax _ ha hb => exact ⟨⟨ha⟩, ⟨hb⟩⟩
  | uniformity ha hh _ hb hb' _ =>
      exact ⟨⟨.iter ha hb⟩, ⟨.iter (.let₁ ha hh) hb'⟩⟩

noncomputable def leftTyping {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ}
    (e : Eqv (τ := τ) (ν := ν) (Φ := Φ) (ε := ε)
    pureEff Γ β a b A) : HasType (τ := τ) (ν := ν) Φ Γ β a A :=
  Classical.choice (e.typable.1)

noncomputable def rightTyping {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ}
    (e : Eqv (τ := τ) (ν := ν) (Φ := Φ) (ε := ε)
    pureEff Γ β a b A) : HasType (τ := τ) (ν := ν) Φ Γ β b A :=
  Classical.choice (e.typable.2)

end Eqv

namespace Categorical

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  (M : Semantics.Categorical.TypeModel τ V)
  [Semantics.Categorical.InstructionModel J M Φ]

/-- The still-open *syntax-to-combinator* obligations, isolated from the
generic proof that semantic equality is a congruence.  The bare fixpoint,
naturality, codiagonal, pure-uniformity, and strength diagrams are not model
axioms: they are derived in `Semantics.IterationDiagrams`.  `core` remains the
claim that the concrete environment-threading interpretation reduces each raw
syntax scheme to those categorical diagrams (together with the structural and
sequencing laws).  `uniformity` likewise retains only that reduction step and
exposes the sound commuting-square induction hypothesis. -/
class LawfulModel : Prop where
  structural {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a b : Tm ν Φ n} {A : τ} (hax : StructuralAxiom pureEff a b)
      (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
    denote J M ha = denote J M hb
  sequencing {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a b : Tm ν Φ n} {A : τ} (hax : SequencingAxiom pureEff a b)
      (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
    denote J M ha = denote J M hb
  contextualIteration {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a b : Tm ν Φ n} {A : τ} (hax : IterationAxiom pureEff a b)
      (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
    denote J M ha = denote J M hb
  uniformity {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)} {A A' B : τ}
      (ha : HasType Φ Γ β a A)
      (hh : HasType Φ Γ (.snoc β A) h A') (hp : Pure pureEff h)
      (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A))
      (hb' : HasType Φ Γ (.snoc β A') b' (LambdaIter.coprod B A'))
      (square : Eqv pureEff Γ (.snoc β A)
        (.case b (.inl (.bv (0 : Fin (n + 2))))
          (.inr (Isotope.LambdaIter.LocallyNameless.Tm.underBinder h)))
        (Isotope.LambdaIter.LocallyNameless.Tm.instantiate
          (Isotope.LambdaIter.LocallyNameless.Tm.underBinder b') h)
        (LambdaIter.coprod B A'))
      (squareSound : denote J M square.leftTyping = denote J M square.rightTyping) :
    denote J M (.iter ha hb) = denote J M (.iter (.let₁ ha hh) hb')

variable [TypingCoherent (τ := τ) (ν := ν) (Φ := Φ) J M]
  [LawfulModel (τ := τ) (ν := ν) (Φ := Φ) (ε := ε)
    (pureEff := pureEff) J M]

/-- Semantic equality is closed under every coercion-free term former. The
only non-congruence work is delegated to the explicitly enumerated lawful
model diagrams above. -/
theorem sound (e : Eqv (τ := τ) (ν := ν) (Φ := Φ) (ε := ε)
    pureEff Γ β a b A) :
    denote J M e.leftTyping = denote J M e.rightTyping := by
  induction e with
  | refl h => rfl
  | symm _ ih => exact ih.symm
  | trans h k ih ik =>
      exact ih.trans ((TypingCoherent.denote_eq h.rightTyping k.leftTyping).trans ik)
  | op h ih =>
      have ih' :
          Semantics.Categorical.denote J M h.leftTyping.toGeneric =
            Semantics.Categorical.denote J M h.rightTyping.toGeneric := ih
      calc
        _ = denote J M (.op h.leftTyping) := TypingCoherent.denote_eq _ _
        _ = denote J M (.op h.rightTyping) := by
          simpa only [denote, HasType.toGeneric,
            Semantics.Categorical.denote] using congrArg
            (fun q => q ≫ Semantics.Categorical.InstructionModel.denote _) ih'
        _ = _ := TypingCoherent.denote_eq _ _
  | let₁ ha hb iha ihb =>
      have iha' :
          Semantics.Categorical.denote J M ha.leftTyping.toGeneric =
            Semantics.Categorical.denote J M ha.rightTyping.toGeneric := iha
      have ihb' :
          Semantics.Categorical.denote J M hb.leftTyping.toGeneric =
            Semantics.Categorical.denote J M hb.rightTyping.toGeneric := ihb
      calc
        _ = denote J M (.let₁ ha.leftTyping hb.leftTyping) :=
          TypingCoherent.denote_eq _ _
        _ = denote J M (.let₁ ha.rightTyping hb.rightTyping) := by
          simp only [denote, HasType.toGeneric, Semantics.Categorical.denote]
          rw [iha', ihb']
        _ = _ := TypingCoherent.denote_eq _ _
  | unit => rfl
  | pair ha hb iha ihb =>
      have iha' :
          Semantics.Categorical.denote J M ha.leftTyping.toGeneric =
            Semantics.Categorical.denote J M ha.rightTyping.toGeneric := iha
      have ihb' :
          Semantics.Categorical.denote J M hb.leftTyping.toGeneric =
            Semantics.Categorical.denote J M hb.rightTyping.toGeneric := ihb
      calc
        _ = denote J M (.pair ha.leftTyping hb.leftTyping) :=
          TypingCoherent.denote_eq _ _
        _ = denote J M (.pair ha.rightTyping hb.rightTyping) := by
          simp only [denote, HasType.toGeneric, Semantics.Categorical.denote]
          rw [iha', ihb']
        _ = _ := TypingCoherent.denote_eq _ _
  | let₂ he hc ihe ihc =>
      have ihe' :
          Semantics.Categorical.denote J M he.leftTyping.toGeneric =
            Semantics.Categorical.denote J M he.rightTyping.toGeneric := ihe
      have ihc' :
          Semantics.Categorical.denote J M hc.leftTyping.toGeneric =
            Semantics.Categorical.denote J M hc.rightTyping.toGeneric := ihc
      calc
        _ = denote J M (.let₂ he.leftTyping hc.leftTyping) :=
          TypingCoherent.denote_eq _ _
        _ = denote J M (.let₂ he.rightTyping hc.rightTyping) := by
          simp only [denote, HasType.toGeneric, Semantics.Categorical.denote]
          rw [ihe', ihc']
        _ = _ := TypingCoherent.denote_eq _ _
  | inl h ih =>
      have ih' :
          Semantics.Categorical.denote J M h.leftTyping.toGeneric =
            Semantics.Categorical.denote J M h.rightTyping.toGeneric := ih
      calc
        _ = denote J M (.inl h.leftTyping) := TypingCoherent.denote_eq _ _
        _ = denote J M (.inl h.rightTyping) := by
          simp only [denote, HasType.toGeneric, Semantics.Categorical.denote]
          rw [ih']
        _ = _ := TypingCoherent.denote_eq _ _
  | inr h ih =>
      have ih' :
          Semantics.Categorical.denote J M h.leftTyping.toGeneric =
            Semantics.Categorical.denote J M h.rightTyping.toGeneric := ih
      calc
        _ = denote J M (.inr h.leftTyping) := TypingCoherent.denote_eq _ _
        _ = denote J M (.inr h.rightTyping) := by
          simp only [denote, HasType.toGeneric, Semantics.Categorical.denote]
          rw [ih']
        _ = _ := TypingCoherent.denote_eq _ _
  | case he hl hr ihe ihl ihr =>
      have ihe' :
          Semantics.Categorical.denote J M he.leftTyping.toGeneric =
            Semantics.Categorical.denote J M he.rightTyping.toGeneric := ihe
      have ihl' :
          Semantics.Categorical.denote J M hl.leftTyping.toGeneric =
            Semantics.Categorical.denote J M hl.rightTyping.toGeneric := ihl
      have ihr' :
          Semantics.Categorical.denote J M hr.leftTyping.toGeneric =
            Semantics.Categorical.denote J M hr.rightTyping.toGeneric := ihr
      calc
        _ = denote J M (.case he.leftTyping hl.leftTyping hr.leftTyping) :=
          TypingCoherent.denote_eq _ _
        _ = denote J M (.case he.rightTyping hl.rightTyping hr.rightTyping) := by
          simp only [denote, HasType.toGeneric, Semantics.Categorical.denote]
          rw [ihe', ihl', ihr']
        _ = _ := TypingCoherent.denote_eq _ _
  | abort h ih =>
      have ih' :
          Semantics.Categorical.denote J M h.leftTyping.toGeneric =
            Semantics.Categorical.denote J M h.rightTyping.toGeneric := ih
      calc
        _ = denote J M (.abort h.leftTyping) := TypingCoherent.denote_eq _ _
        _ = denote J M (.abort h.rightTyping) := by
          simp only [denote, HasType.toGeneric, Semantics.Categorical.denote]
          rw [ih']
        _ = _ := TypingCoherent.denote_eq _ _
  | iter ha hb iha ihb =>
      have iha' :
          Semantics.Categorical.denote J M ha.leftTyping.toGeneric =
            Semantics.Categorical.denote J M ha.rightTyping.toGeneric := iha
      have ihb' :
          Semantics.Categorical.denote J M hb.leftTyping.toGeneric =
            Semantics.Categorical.denote J M hb.rightTyping.toGeneric := ihb
      calc
        _ = denote J M (.iter ha.leftTyping hb.leftTyping) :=
          TypingCoherent.denote_eq _ _
        _ = denote J M (.iter ha.rightTyping hb.rightTyping) := by
          simp only [denote, HasType.toGeneric, Semantics.Categorical.denote]
          rw [iha', ihb']
        _ = _ := TypingCoherent.denote_eq _ _
  | ax hax ha hb =>
      exact (TypingCoherent.denote_eq _ ha).trans <| match hax with
        | .structural h =>
            (LawfulModel.structural h ha hb).trans (TypingCoherent.denote_eq hb _)
        | .sequencing h =>
            (LawfulModel.sequencing h ha hb).trans (TypingCoherent.denote_eq hb _)
        | .iteration h =>
            (LawfulModel.contextualIteration h ha hb).trans
              (TypingCoherent.denote_eq hb _)
  | uniformity ha hh hp hb hb' square ih =>
      exact (TypingCoherent.denote_eq _ (.iter ha hb)).trans <|
        (LawfulModel.uniformity ha hh hp hb hb' square ih).trans
          (TypingCoherent.denote_eq (.iter (.let₁ ha hh) hb') _)

/-- Soundness for arbitrary endpoint typing derivations follows from typing
coherence and the canonical endpoint theorem. -/
theorem sound_between (e : Eqv (τ := τ) (ν := ν) (Φ := Φ) (ε := ε)
    pureEff Γ β a b A)
    (ha : HasType (τ := τ) (ν := ν) Φ Γ β a A)
    (hb : HasType (τ := τ) (ν := ν) Φ Γ β b A) :
    denote J M ha = denote J M hb :=
  (TypingCoherent.denote_eq ha e.leftTyping).trans <|
    (sound J M e).trans (TypingCoherent.denote_eq e.rightTyping hb)

end Categorical

end Isotope.LambdaIter.NoSubtyping.LocallyNameless
