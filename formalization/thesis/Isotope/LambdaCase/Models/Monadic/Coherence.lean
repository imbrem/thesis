import Isotope.LambdaIter.Models.Monadic.Coupling
import Isotope.LambdaCase.Models.Monadic.Denotation

/-!
# Coherence of the lambda-case denotation in its typing derivation

Lambda-case typing is *not* unique: `abort` types at every result type, and
`inl` leaves the right summand free.  So two derivations of one term at one
type can have sub-derivations at genuinely different types, and the
interpretation must be shown not to notice.

The proof is a coupling (parametricity) argument, stated over derivations in
*two* bound contexts with related environments; see
`Isotope/LambdaIter/Models/Monadic/Coupling.lean` for why relatedness of
computations must be phrased as a span rather than as a relation.
-/

namespace Isotope.LambdaCase.Monadic

open LocallyNameless

open Isotope.LambdaIter (Sig instrSrc instrTrg TypeFormers InjectiveFormers)
open Isotope.LambdaIter.Monadic
open Isotope.LambdaIter.Monadic.SeqModel

universe u v

variable {S : Sig.{u}} {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [InjectiveFormers S.Ty]

/-- **The coupling theorem.**  Any two derivations of one term, in two bound
contexts, interpreted at related environments, denote coupled computations. -/
theorem denote_coupled (M : Model.{u, v} S m) {n : Nat}
    {β₁ : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A₁ : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β₁ t A₁) :
    ∀ {β₂ : BoundCtx S.Ty n} {A₂ : S.Ty}
      (k : HasType S.Instr LambdaIter.Ctx.nil β₂ t A₂)
      (ρ₁ : M.Env β₁) (ρ₂ : M.Env β₂), EnvRel M ρ₁ ρ₂ →
      Coupled M (denote M h ρ₁) (denote M k ρ₂) := by
  induction h with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv =>
      intro β₂ A₂ k ρ₁ ρ₂ hρ
      cases k
      exact Coupled.pure' (hρ _)
  | op h ih =>
      intro β₂ A₂ k ρ₁ ρ₂ hρ
      cases k with
      | op k' =>
          refine (ih k' ρ₁ ρ₂ hρ).bind' fun p => ?_
          rw [p.property.eq_of]
          exact Coupled.refl' _
  | let₁ ha hb iha ihb =>
      intro β₂ A₂ k ρ₁ ρ₂ hρ
      cases k with
      | let₁ ka kb =>
          exact (iha ka ρ₁ ρ₂ hρ).bind' fun p =>
            ihb kb (ρ₁, p.val.1) (ρ₂, p.val.2) (hρ.snoc p.property)
  | unit =>
      intro β₂ A₂ k ρ₁ ρ₂ _
      cases k
      exact Coupled.pure' (.same _)
  | pair ha hb iha ihb =>
      intro β₂ A₂ k ρ₁ ρ₂ hρ
      cases k with
      | pair ka kb =>
          exact (iha ka ρ₁ ρ₂ hρ).bind' fun p =>
            (ihb kb ρ₁ ρ₂ hρ).bind' fun q =>
              Coupled.pure' (.pair p.property q.property)
  | let₂ ha hc iha ihc =>
      intro β₂ A₂ k ρ₁ ρ₂ hρ
      cases k with
      | let₂ ka kc =>
          refine (iha ka ρ₁ ρ₂ hρ).bind' fun p => ?_
          obtain ⟨h1, h2⟩ := p.property.tensor_inv
          exact ihc kc _ _ ((hρ.snoc h1).snoc h2)
  | inl h ih =>
      intro β₂ A₂ k ρ₁ ρ₂ hρ
      cases k with
      | inl k' =>
          exact (ih k' ρ₁ ρ₂ hρ).bind' fun p => Coupled.pure' (.left p.property)
  | inr h ih =>
      intro β₂ A₂ k ρ₁ ρ₂ hρ
      cases k with
      | inr k' =>
          exact (ih k' ρ₁ ρ₂ hρ).bind' fun p => Coupled.pure' (.right p.property)
  | case he hl hr ihe ihl ihr =>
      intro β₂ A₂ k ρ₁ ρ₂ hρ
      cases k with
      | case ke kl kr =>
          refine (ihe ke ρ₁ ρ₂ hρ).bind' fun p => ?_
          rcases p.property.coprod_inv with ⟨a, a', ha, ha', hab⟩ |
            ⟨b, b', hb, hb', hab⟩
          · simp only [ha, ha']
            exact ihl kl (ρ₁, a) (ρ₂, a') (hρ.snoc hab)
          · simp only [hb, hb']
            exact ihr kr (ρ₁, b) (ρ₂, b') (hρ.snoc hab)
  | abort h ih =>
      intro β₂ A₂ k ρ₁ ρ₂ hρ
      cases k with
      | abort k' =>
          exact (ih k' ρ₁ ρ₂ hρ).bind' fun p => (M.emptyEquiv p.val.1).elim

/-- **Coherence**: the denotation of a term does not depend on its typing
derivation.  This is the `coh` field of `Alg`. -/
theorem denote_coh (M : Model.{u, v} S m) {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h k : HasType S.Instr LambdaIter.Ctx.nil β t A) (ρ : M.Env β) :
    denote M h ρ = denote M k ρ :=
  (denote_coupled M h k ρ ρ (EnvRel.refl' ρ)).eq

end Isotope.LambdaCase.Monadic
