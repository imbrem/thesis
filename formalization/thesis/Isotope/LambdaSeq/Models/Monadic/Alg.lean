import Isotope.LambdaSeq.Models.Monadic.Denotation

/-!
# Every monad gives an algebra of the lambda-seq presentation

This file closes, for lambda-seq, the gap recorded in `Models/Alg.lean`: the
two propositional fields `coh` and `sound` of `Alg` are discharged for the
monadic denotation, so `Alg.ofSeqModel` turns a monad with an interpretation of
the signature into an object of `Alg S`.

## The two obligations

* **`coh`** is the statement that the denotation does not depend on the chosen
  typing derivation.  It is *not* automatic: lambda-seq typing happens to be
  unique (`HasType.uniq`), and that is what makes the proof short here; the
  same field for lambda-case and lambda-iter needs a genuine argument, because
  `abort` types at every result type.  The proof below goes through the
  stronger cross-type statement `denote_agree` anyway, so it transfers.
* **`sound`** is soundness for `Equiv`.  Its proof rewrites *both* given
  derivations to canonical ones built from the data of the equation itself
  (using `coh`), and only then argues.  That is what keeps the intermediate
  types of the derivations aligned with the intermediate types of the
  equation.

## Hypotheses

`[Monad m]` and `[LawfulMonad m]`, and nothing else: no `Iterate`, no
`LawfulElgotMonad`, and no type former.  This is the weakest of the three
bridges, as it must be.
-/

namespace Isotope.LambdaSeq

open LocallyNameless

open Isotope.LambdaIter (Sig instrSrc instrTrg)
open Isotope.LambdaIter.Monadic
open Isotope.LambdaIter.Monadic.SeqModel

universe u v uτ wν qΦ

namespace LocallyNameless

variable {τ : Type uτ} [LambdaIter.TypeFormers τ]
variable {ν : Type wν} [DecidableEq ν]
variable {Φ : Type qΦ} [LambdaIter.HasTy Φ τ]
variable {Γ : Ctx ν τ}

/-- **Lambda-seq has unique typing.**  Every term has at most one type in a
given context; unlike lambda-case and lambda-iter there is no `abort`, whose
result type is unconstrained. -/
theorem HasType.uniq : {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} →
    {A₁ A₂ : τ} → HasType Φ Γ β t A₁ → HasType Φ Γ β t A₂ → A₁ = A₂
  | _, _, _, _, _, .fv h₁, .fv h₂ => by
      rw [h₁] at h₂; exact Option.some.inj h₂
  | _, _, _, _, _, .bv, .bv => rfl
  | _, _, _, _, _, .op _, .op _ => rfl
  | _, _, _, _, _, .let₁ ha hb, .let₁ ka kb => by
      cases HasType.uniq ha ka
      exact HasType.uniq hb kb

end LocallyNameless

namespace Monadic

variable {S : Sig.{u}} {m : Type v → Type v} [Monad m] [LawfulMonad m]

/-- **Cross-type coherence.**  Two derivations of the same term denote the same
computation *modulo their continuations*: whenever the continuations agree on
the nose in case the two result types coincide, the two bound computations are
equal.  The hypothesis is vacuous when the types differ, which is exactly the
strength needed for calculi whose typing is not unique. -/
theorem denote_agree (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A₁ : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A₁) :
    ∀ {A₂ : S.Ty} (k : HasType S.Instr LambdaIter.Ctx.nil β t A₂)
      (ρ : M.Env β) {X : Type v} (f : M.interp A₁ → m X)
      (g : M.interp A₂ → m X),
      (∀ (e : A₁ = A₂) (x : M.interp A₁), f x = g (e ▸ x)) →
      denote M h ρ >>= f = denote M k ρ >>= g := by
  induction h with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv =>
      intro A₂ k ρ X f g hfg
      cases k
      change pure _ >>= f = pure _ >>= g
      rw [pure_bind, pure_bind]
      exact hfg rfl _
  | op h ih =>
      intro A₂ k ρ X f g hfg
      cases k with
      | op h' =>
          change (denote M h ρ >>= M.denoteInstr _) >>= f =
            (denote M h' ρ >>= M.denoteInstr _) >>= g
          rw [bind_assoc, bind_assoc]
          exact ih h' ρ _ _ fun _ x => bind_congr fun y => hfg rfl y
  | let₁ ha hb iha ihb =>
      intro A₂ k ρ X f g hfg
      cases k with
      | let₁ ka kb =>
          change (denote M ha ρ >>= fun x => denote M hb (ρ, x)) >>= f =
            (denote M ka ρ >>= fun x => denote M kb (ρ, x)) >>= g
          rw [bind_assoc, bind_assoc]
          refine iha ka ρ _ _ ?_
          intro e x
          cases e
          exact ihb kb (ρ, x) f g hfg

/-- **Coherence**: the denotation of a term does not depend on its typing
derivation. -/
theorem denote_coh (M : SeqModel.{u, v} S m) {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h k : HasType S.Instr LambdaIter.Ctx.nil β t A) (ρ : M.Env β) :
    denote M h ρ = denote M k ρ := by
  have hb := denote_agree M h k ρ pure pure fun _ _ => rfl
  rwa [bind_pure, bind_pure] at hb

section Axioms

variable (M : SeqModel.{u, v} S m) {n : Nat} {β : BoundCtx S.Ty n}

/-- Soundness of the beta law for `let`. -/
theorem sound_letBeta {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    {A B : S.Ty} (hp : Pure S.pureEff a)
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a A)
    (hb : HasType S.Instr LambdaIter.Ctx.nil (.snoc β A) b B) (ρ : M.Env β) :
    denote M (.let₁ ha hb) ρ = denote M (hb.instantiate ha) ρ := by
  obtain ⟨x, hx⟩ := denote_pure_factor M hp ha ρ
  rw [denote_let₁, hx, pure_bind, denote_instantiate M hb ha ρ x hx]

/-- Soundness of the eta law for `let`. -/
theorem sound_letEta {a : Tm Empty S.Instr n} {A : S.Ty}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a A) (ρ : M.Env β) :
    denote M (.let₁ ha HasType.newest) ρ = denote M ha ρ := by
  rw [denote_let₁]
  simp only [denote_newest]
  exact bind_pure _

/-- Soundness of the instruction-sequencing law. -/
theorem sound_bindOp {f : S.Instr} {a : Tm Empty S.Instr n}
    {c : Tm Empty S.Instr (n + 1)} {C : S.Ty}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a (instrSrc f))
    (hc : HasType S.Instr LambdaIter.Ctx.nil (.snoc β (instrTrg f)) c C)
    (ρ : M.Env β) :
    denote M (.let₁ (.op ha) hc) ρ =
      denote M (.let₁ ha (.let₁ (.op HasType.newest) hc.underBinder)) ρ := by
  simp only [denote_let₁, denote_op, denote_newest, pure_bind, bind_assoc,
    denote_underBinder]

/-- Soundness of the associativity law for `let`. -/
theorem sound_bindLet {a : Tm Empty S.Instr n} {b c : Tm Empty S.Instr (n + 1)}
    {A B C : S.Ty} (ha : HasType S.Instr LambdaIter.Ctx.nil β a A)
    (hb : HasType S.Instr LambdaIter.Ctx.nil (.snoc β A) b B)
    (hc : HasType S.Instr LambdaIter.Ctx.nil (.snoc β B) c C) (ρ : M.Env β) :
    denote M (.let₁ (.let₁ ha hb) hc) ρ =
      denote M (.let₁ ha (.let₁ hb hc.underBinder)) ρ := by
  simp only [denote_let₁, bind_assoc, denote_underBinder]

end Axioms

/-- **Soundness**: the monadic denotation respects the lambda-seq equational
theory.  The proof replaces both given derivations by canonical ones built from
the equation's own data, which is what aligns their intermediate types. -/
theorem sound (M : SeqModel.{u, v} S m) {n : Nat} {β : BoundCtx S.Ty n}
    {a b : Tm Empty S.Instr n} {A : S.Ty}
    (he : Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β a b A) :
    ∀ (h : HasType S.Instr LambdaIter.Ctx.nil β a A)
      (k : HasType S.Instr LambdaIter.Ctx.nil β b A) (ρ : M.Env β),
      denote M h ρ = denote M k ρ := by
  induction he with
  | var h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bvar => intro h k ρ; exact denote_coh M h k ρ
  | symm _ ih => intro h k ρ; exact (ih k h ρ).symm
  | trans hab _ ih₁ ih₂ =>
      intro h k ρ
      obtain ⟨hb⟩ := hab.regular.2
      exact (ih₁ h hb ρ).trans (ih₂ hb k ρ)
  | op hop ih =>
      intro h k ρ
      obtain ⟨hA⟩ := hop.regular.1
      obtain ⟨hA'⟩ := hop.regular.2
      rw [denote_coh M h (.op hA) ρ, denote_coh M k (.op hA') ρ]
      exact congrArg (fun z => z >>= M.denoteInstr _) (ih hA hA' ρ)
  | let₁ hae hbe ih₁ ih₂ =>
      intro h k ρ
      obtain ⟨hA⟩ := hae.regular.1
      obtain ⟨hA'⟩ := hae.regular.2
      obtain ⟨hB⟩ := hbe.regular.1
      obtain ⟨hB'⟩ := hbe.regular.2
      rw [denote_coh M h (.let₁ hA hB) ρ, denote_coh M k (.let₁ hA' hB') ρ]
      change denote M hA ρ >>= (fun x => denote M hB (ρ, x)) =
        denote M hA' ρ >>= fun x => denote M hB' (ρ, x)
      rw [ih₁ hA hA' ρ]
      exact bind_congr fun x => ih₂ hB hB' (ρ, x)
  | letBeta hp ha hb =>
      intro h k ρ
      rw [denote_coh M h (.let₁ ha hb) ρ,
        denote_coh M k (hb.instantiate ha) ρ]
      exact sound_letBeta M hp ha hb ρ
  | letEta ha =>
      intro h k ρ
      rw [denote_coh M h (.let₁ ha HasType.newest) ρ, denote_coh M k ha ρ]
      exact sound_letEta M ha ρ
  | bindOp ha hc =>
      intro h k ρ
      rw [denote_coh M h (.let₁ (.op ha) hc) ρ,
        denote_coh M k (.let₁ ha (.let₁ (.op HasType.newest) hc.underBinder)) ρ]
      exact sound_bindOp M ha hc ρ
  | bindLet ha hb hc =>
      intro h k ρ
      rw [denote_coh M h (.let₁ (.let₁ ha hb) hc) ρ,
        denote_coh M k (.let₁ ha (.let₁ hb hc.underBinder)) ρ]
      exact sound_bindLet M ha hb hc ρ

/-- The operations of the monadic model: the clauses of `denote`, read as
operations on Kleisli computations. -/
def ops (M : SeqModel.{u, v} S m) : Alg.Ops.{u, v} S where
  El β A := M.Env β → m (M.interp A)
  var i := fun ρ => pure (Env.get ρ i)
  op f x := fun ρ => x ρ >>= M.denoteInstr f
  let₁ x y := fun ρ => x ρ >>= fun a => y (ρ, a)

/-- The interpretation of a derivation by `ops` is the monadic denotation. -/
@[simp] theorem ops_denote (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    (ops M).denote h = denote M h := by
  induction h with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv => rfl
  | op h ih =>
      funext ρ
      change (ops M).denote h ρ >>= M.denoteInstr _ = denote M h ρ >>= _
      rw [ih]
  | let₁ ha hb iha ihb =>
      funext ρ
      change (ops M).denote ha ρ >>= (fun a => (ops M).denote hb (ρ, a)) =
        denote M ha ρ >>= fun a => denote M hb (ρ, a)
      rw [iha, ihb]

/-- **The bridge for lambda-seq.**  Every lawful monad with an interpretation
of the signature's types and instructions is an algebra of the lambda-seq
equational presentation.

The carrier at `β` and `A` is the type of Kleisli computations
`M.Env β → m (M.interp A)`; the operations are the clauses of `denote`.  No
iteration operator and no type former is used. -/
def _root_.Isotope.LambdaSeq.Alg.ofSeqModel (M : SeqModel.{u, v} S m) :
    Alg.{u, v} S where
  toOps := ops M
  coh h k := by rw [ops_denote, ops_denote]; exact funext fun ρ => denote_coh M h k ρ
  sound h k he := by
    rw [ops_denote, ops_denote]; exact funext fun ρ => sound M he h k ρ

/-- The denotation in `Alg.ofSeqModel` is the monadic denotation. -/
@[simp] theorem ofSeqModel_denote (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    (Alg.ofSeqModel M).denote h = denote M h := ops_denote M h

end Monadic
end Isotope.LambdaSeq
