import Isotope.LambdaIter.Models.Monadic.Soundness

/-!
# Every Elgot monad gives an algebra of the lambda-iter presentation

This closes the gap recorded in `Models/Alg.lean` for lambda-iter itself: both
propositional fields of `Alg` are discharged for the monadic denotation, so
`Alg.ofModel` turns a lawful Elgot monad with an interpretation of the
signature into an object of `Alg S`.

## The axiom rule

`Eqv.ax` carries a *raw* `CoreAxiom` together with two typing derivations, so
soundness has to invert those derivations against the axiom's term shape.
Three of those inversions cannot be done by `cases`: a derivation whose result
type is already a composite (`.inl e` at `A ⊕ B`, `.pair a b` at `A ⊗ B`)
forces the equation `A' ⊕ B' = A ⊕ B` on the constructor's own indices, which
dependent elimination can only solve by *injectivity* of the former.  Hence
`HasType.pair_inv`, `.inl_inv`, `.inr_inv` below, which take that equation as
an argument and use `InjectiveFormers`.

For every axiom but the codiagonal, the left-hand term is inverted and the
right-hand derivation is *built* from the pieces; the codiagonal goes the other
way, because there the renaming `underBinder` sits on the left, and typing
derivations transport along a renaming but not back.

## Hypotheses

`[Monad m]`, `[LawfulMonad m]`, `[Iterate m]`, `[LawfulElgotMonad m]` and
`[InjectiveFormers S.Ty]`.  The Elgot laws are used for the four iteration
axioms *and* — through `Coupled.iterate` — for coherence.
-/

namespace Isotope.LambdaIter

open LocallyNameless

open Isotope.Elgot
open Isotope.LambdaIter.Monadic
open Isotope.LambdaIter.Monadic.SeqModel

universe u v uτ wν qΦ

namespace LocallyNameless

variable {τ : Type uτ} [TypeFormers τ] [InjectiveFormers τ]
variable {ν : Type wν} [DecidableEq ν]
variable {Φ : Type qΦ} [HasTy Φ τ]
variable {Γ : LambdaIter.Ctx ν τ}

omit [InjectiveFormers τ] in
/-- The type of a bound variable is the one its context stores. -/
theorem HasType.bv_ty {n : Nat} {β : BoundCtx τ n} {i : Fin n} {A : τ}
    (h : HasType Φ Γ β (.bv i) A) : A = β.get i := by
  cases h
  rfl

/-- Inversion of a pairing derivation at a tensor type.  The type equation is
an explicit argument because dependent elimination cannot solve it: it needs
injectivity of the tensor former. -/
def HasType.pair_inv {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {C A B : τ}
    (h : HasType Φ Γ β (.pair a b) C) (e : C = tensor A B) :
    HasType Φ Γ β a A × HasType Φ Γ β b B := by
  cases h with
  | pair ha hb =>
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.tensor_inj e
      exact ⟨ha, hb⟩

/-- Inversion of a left injection at a coproduct type. -/
def HasType.inl_inv {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {C A B : τ}
    (h : HasType Φ Γ β (.inl a) C) (e : C = coprod A B) :
    HasType Φ Γ β a A := by
  cases h with
  | inl ha =>
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj e
      exact ha

/-- Inversion of a right injection at a coproduct type. -/
def HasType.inr_inv {n : Nat} {β : BoundCtx τ n} {b : Tm ν Φ n} {C A B : τ}
    (h : HasType Φ Γ β (.inr b) C) (e : C = coprod A B) :
    HasType Φ Γ β b B := by
  cases h with
  | inr hb =>
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj e
      exact hb

end LocallyNameless

namespace Monadic

variable {S : Sig.{u}} {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InjectiveFormers S.Ty]

/-- **Soundness of the raw axiom schemes.**  Each case inverts the derivation
of one endpoint, builds a canonical derivation of the other, and appeals to the
corresponding lemma of `Monadic/Soundness.lean`; coherence bridges the given
derivations and the canonical ones. -/
theorem sound_ax (M : Model.{u, v} S m) {n : Nat} {β : BoundCtx S.Ty n}
    {a b : Tm Empty S.Instr n} {A : S.Ty}
    (hax : CoreAxiom S.pureEff a b)
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil β b A) (ρ : M.Env β) :
    denote M ha ρ = denote M hb ρ := by
  cases hax with
  | structural hs =>
      cases hs with
      | letBeta hp =>
          cases ha with
          | let₁ h₁ h₂ =>
              exact (sound_letBeta M hp h₁ h₂ ρ).trans
                (denote_coh M (h₂.instantiate h₁) hb ρ)
      | letEta _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₂
              exact (denote_coh M (.let₁ h₁ HasType.bv)
                  (.let₁ h₁ HasType.newest) ρ).trans
                ((sound_letEta M h₁ ρ).trans (denote_coh M h₁ hb ρ))
      | unitEta _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₂
              exact sound_unitEta M h₁ hb ρ
      | pairBeta _ _ _ =>
          cases ha with
          | let₂ h₁ h₂ =>
              obtain ⟨p₁, p₂⟩ := h₁.pair_inv rfl
              exact (denote_coh M (.let₂ h₁ h₂) (.let₂ (.pair p₁ p₂) h₂) ρ).trans
                ((sound_pairBeta M p₁ p₂ h₂ ρ).trans
                  (denote_coh M (.let₁ p₁ (.let₁ p₂.lift h₂)) hb ρ))
      | pairEta _ =>
          cases ha with
          | let₂ h₁ h₂ =>
              cases h₂ with
              | pair q₁ q₂ =>
                  cases q₁
                  cases q₂
                  exact (denote_coh M (.let₂ h₁ (.pair .bv .bv))
                      (.let₂ h₁ (.pair HasType.previous HasType.newest)) ρ).trans
                    ((sound_pairEta M h₁ ρ).trans (denote_coh M h₁ hb ρ))
      | caseBetaL _ _ _ =>
          cases ha with
          | case h₁ hl hr =>
              have he := h₁.inl_inv rfl
              exact (denote_coh M (.case h₁ hl hr) (.case (.inl he) hl hr) ρ).trans
                ((sound_caseBetaL M he hl hr ρ).trans
                  (denote_coh M (.let₁ he hl) hb ρ))
      | caseBetaR _ _ _ =>
          cases ha with
          | case h₁ hl hr =>
              have he := h₁.inr_inv rfl
              exact (denote_coh M (.case h₁ hl hr) (.case (.inr he) hl hr) ρ).trans
                ((sound_caseBetaR M he hl hr ρ).trans
                  (denote_coh M (.let₁ he hr) hb ρ))
      | caseEta _ =>
          cases ha with
          | case h₁ hl hr =>
              cases hl with
              | inl u =>
                  cases u
                  cases HasType.inr_inv hr rfl
                  exact (denote_coh M (.case h₁ (.inl .bv) hr)
                      (.case h₁ (.inl HasType.newest) (.inr HasType.newest))
                      ρ).trans
                    ((sound_caseEta M h₁ ρ).trans (denote_coh M h₁ hb ρ))
      | emptyInitial _ _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | abort hz =>
                  cases hb with
                  | let₁ k₁ k₂ =>
                      cases k₁ with
                      | abort hz' => exact sound_emptyInitial M hz hz' h₂ k₂ ρ
  | sequencing hs =>
      cases hs with
      | bindOp _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | op haa =>
                  exact (sound_bindOp M haa h₂ ρ).trans (denote_coh M _ hb ρ)
      | bindLet _ _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | let₁ g₁ g₂ =>
                  exact (sound_bindLet M g₁ g₂ h₂ ρ).trans (denote_coh M _ hb ρ)
      | bindLetPair _ _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | let₂ g₁ g₂ =>
                  exact (sound_bindLetPair M g₁ g₂ h₂ ρ).trans
                    (denote_coh M _ hb ρ)
      | bindLetCase _ _ _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | case g₁ g₂ g₃ =>
                  exact (sound_bindLetCase M g₁ g₂ g₃ h₂ ρ).trans
                    (denote_coh M _ hb ρ)
      | bindPair _ _ =>
          cases ha with
          | let₂ h₁ h₂ =>
              exact (sound_bindPair M h₁ h₂ ρ).trans (denote_coh M _ hb ρ)
      | bindCase _ _ _ =>
          cases ha with
          | case h₁ hl hr =>
              exact (sound_bindCase M h₁ hl hr ρ).trans (denote_coh M _ hb ρ)
  | iteration hi =>
      cases hi with
      | fixpoint _ _ =>
          cases ha with
          | iter h₁ h₂ =>
              exact (sound_iterFixpoint M h₁ h₂ ρ).trans (denote_coh M _ hb ρ)
      | naturality _ _ _ =>
          cases ha with
          | let₁ h₁ h₂ =>
              cases h₁ with
              | iter g₁ g₂ =>
                  exact (sound_iterNaturality M g₁ g₂ h₂ ρ).trans
                    (denote_coh M _ hb ρ)
      | codiagonal _ _ =>
          cases hb with
          | iter k₁ k₂ =>
              cases k₂ with
              | case c₁ c₂ c₃ =>
                  cases c₂
                  obtain rfl : _ = _ :=
                    HasType.bv_ty (HasType.inr_inv c₃ rfl)
                  exact (denote_coh M ha
                      (.iter k₁ (.iter HasType.newest c₁.underBinder)) ρ).trans
                    ((sound_iterCodiagonal M k₁ c₁ ρ).trans
                      (denote_coh M
                        (.iter k₁ (.case c₁ HasType.newest
                          (.inr HasType.newest))) _ ρ))
      | iterBind _ _ =>
          cases ha with
          | iter h₁ h₂ =>
              exact (sound_iterBind M h₁ h₂ ρ).trans (denote_coh M _ hb ρ)


/-- **Soundness**: the monadic denotation respects the lambda-iter equational
theory `Eqv`.  Congruence cases replace both given derivations by canonical
ones built from the equation's own data; the axiom rule is `sound_ax`; the
uniformity rule is `sound_iterUniformity`, whose commuting square is supplied
by the induction hypothesis. -/
theorem sound (M : Model.{u, v} S m) {n : Nat} {β : BoundCtx S.Ty n}
    {a b : Tm Empty S.Instr n} {A : S.Ty}
    (he : Eqv (Φ := S.Instr) S.pureEff Ctx.nil β a b A) :
    ∀ (h : HasType S.Instr Ctx.nil β a A)
      (k : HasType S.Instr Ctx.nil β b A) (ρ : M.Env β),
      denote M h ρ = denote M k ρ := by
  induction he with
  | refl _ => intro h k ρ; exact denote_coh M h k ρ
  | symm _ ih => intro h k ρ; exact (ih k h ρ).symm
  | trans hab _ ih₁ ih₂ =>
      intro h k ρ
      obtain ⟨hm⟩ := hab.regular.2
      exact (ih₁ h hm ρ).trans (ih₂ hm k ρ)
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
      rw [denote_coh M h (.let₁ hA hB) ρ, denote_coh M k (.let₁ hA' hB') ρ,
        denote_let₁, denote_let₁, ih₁ hA hA' ρ]
      exact bind_congr fun x => ih₂ hB hB' (ρ, x)
  | unit => intro h k ρ; exact denote_coh M h k ρ
  | pair hae hbe ih₁ ih₂ =>
      intro h k ρ
      obtain ⟨hA⟩ := hae.regular.1
      obtain ⟨hA'⟩ := hae.regular.2
      obtain ⟨hB⟩ := hbe.regular.1
      obtain ⟨hB'⟩ := hbe.regular.2
      rw [denote_coh M h (.pair hA hB) ρ, denote_coh M k (.pair hA' hB') ρ,
        denote_pair, denote_pair, ih₁ hA hA' ρ]
      exact bind_congr fun x => by rw [ih₂ hB hB' ρ]
  | let₂ hae hce ih₁ ih₂ =>
      intro h k ρ
      obtain ⟨hA⟩ := hae.regular.1
      obtain ⟨hA'⟩ := hae.regular.2
      obtain ⟨hC⟩ := hce.regular.1
      obtain ⟨hC'⟩ := hce.regular.2
      rw [denote_coh M h (.let₂ hA hC) ρ, denote_coh M k (.let₂ hA' hC') ρ,
        denote_let₂, denote_let₂, ih₁ hA hA' ρ]
      exact bind_congr fun ab => ih₂ hC hC' _
  | inl hae ih =>
      intro h k ρ
      obtain ⟨hA⟩ := hae.regular.1
      obtain ⟨hA'⟩ := hae.regular.2
      rw [denote_coh M h (.inl hA) ρ, denote_coh M k (.inl hA') ρ,
        denote_inl, denote_inl, ih hA hA' ρ]
  | inr hbe ih =>
      intro h k ρ
      obtain ⟨hB⟩ := hbe.regular.1
      obtain ⟨hB'⟩ := hbe.regular.2
      rw [denote_coh M h (.inr hB) ρ, denote_coh M k (.inr hB') ρ,
        denote_inr, denote_inr, ih hB hB' ρ]
  | case hee hle hre ihe ihl ihr =>
      intro h k ρ
      obtain ⟨hE⟩ := hee.regular.1
      obtain ⟨hE'⟩ := hee.regular.2
      obtain ⟨hL⟩ := hle.regular.1
      obtain ⟨hL'⟩ := hle.regular.2
      obtain ⟨hR⟩ := hre.regular.1
      obtain ⟨hR'⟩ := hre.regular.2
      rw [denote_coh M h (.case hE hL hR) ρ,
        denote_coh M k (.case hE' hL' hR') ρ, denote_case, denote_case,
        ihe hE hE' ρ]
      refine bind_congr fun e => ?_
      cases M.coprodEquiv _ _ e with
      | inl x => exact ihl hL hL' (ρ, x)
      | inr y => exact ihr hR hR' (ρ, y)
  | abort hae ih =>
      intro h k ρ
      obtain ⟨hA⟩ := hae.regular.1
      obtain ⟨hA'⟩ := hae.regular.2
      rw [denote_coh M h (.abort hA) ρ, denote_coh M k (.abort hA') ρ,
        denote_abort, denote_abort, ih hA hA' ρ]
  | iter hae hbe ih₁ ih₂ =>
      intro h k ρ
      obtain ⟨hA⟩ := hae.regular.1
      obtain ⟨hA'⟩ := hae.regular.2
      obtain ⟨hB⟩ := hbe.regular.1
      obtain ⟨hB'⟩ := hbe.regular.2
      rw [denote_coh M h (.iter hA hB) ρ, denote_coh M k (.iter hA' hB') ρ,
        denote_iter, denote_iter, ih₁ hA hA' ρ]
      refine bind_congr fun x => ?_
      congr 1
      funext y
      rw [ih₂ hB hB' (ρ, y)]
  | ax hax ha hb =>
      intro h k ρ
      rw [denote_coh M h ha ρ, denote_coh M k hb ρ]
      exact sound_ax M hax ha hb ρ
  | uniformity ha hh hp hb hb' _ ih =>
      intro h k ρ
      rw [denote_coh M h (.iter ha hb) ρ,
        denote_coh M k (.iter (.let₁ ha hh) hb') ρ]
      exact sound_iterUniformity M ha hh hp hb hb' (fun ρA => ih _ _ ρA) ρ

/-- The operations of the monadic model: the clauses of `denote`, read as
operations on Kleisli computations. -/
def ops (M : Model.{u, v} S m) : Alg.Ops.{u, v} S where
  El β A := M.Env β → m (M.interp A)
  var i := fun ρ => pure (Env.get ρ i)
  op f x := fun ρ => x ρ >>= M.denoteInstr f
  let₁ x y := fun ρ => x ρ >>= fun a => y (ρ, a)
  unit := fun _ => pure (M.unitEquiv.symm ())
  pair x y := fun ρ => x ρ >>= fun a => y ρ >>= fun b =>
    pure ((M.tensorEquiv _ _).symm (a, b))
  let₂ x y := fun ρ => x ρ >>= fun ab =>
    y ((ρ, (M.tensorEquiv _ _ ab).1), (M.tensorEquiv _ _ ab).2)
  inl x := fun ρ => x ρ >>= fun a => pure ((M.coprodEquiv _ _).symm (.inl a))
  inr x := fun ρ => x ρ >>= fun b => pure ((M.coprodEquiv _ _).symm (.inr b))
  case x y z := fun ρ => x ρ >>= fun e =>
    match M.coprodEquiv _ _ e with
    | .inl a => y (ρ, a)
    | .inr b => z (ρ, b)
  abort x := fun ρ => x ρ >>= fun z => Empty.elim (M.emptyEquiv z)
  iter x y := fun ρ => x ρ >>= Elgot.iter fun a =>
    y (ρ, a) >>= fun s => pure (M.coprodEquiv _ _ s)

/-- The interpretation of a derivation by `ops` is the monadic denotation. -/
@[simp] theorem ops_denote (M : Model.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) :
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
  | unit => rfl
  | pair ha hb iha ihb =>
      funext ρ
      change (ops M).denote ha ρ >>= (fun a => (ops M).denote hb ρ >>= fun b =>
        pure ((M.tensorEquiv _ _).symm (a, b))) = _
      rw [iha, ihb]
      rfl
  | let₂ ha hc iha ihc =>
      funext ρ
      change (ops M).denote ha ρ >>= (fun ab => (ops M).denote hc
        ((ρ, (M.tensorEquiv _ _ ab).1), (M.tensorEquiv _ _ ab).2)) = _
      rw [iha, ihc]
      rfl
  | inl h ih =>
      funext ρ
      change (ops M).denote h ρ >>= (fun a =>
        pure ((M.coprodEquiv _ _).symm (.inl a))) = _
      rw [ih]
      rfl
  | inr h ih =>
      funext ρ
      change (ops M).denote h ρ >>= (fun b =>
        pure ((M.coprodEquiv _ _).symm (.inr b))) = _
      rw [ih]
      rfl
  | case he hl hr ihe ihl ihr =>
      funext ρ
      change (ops M).denote he ρ >>= (fun e =>
        match M.coprodEquiv _ _ e with
        | .inl a => (ops M).denote hl (ρ, a)
        | .inr b => (ops M).denote hr (ρ, b)) = _
      rw [ihe, ihl, ihr]
      rfl
  | abort h ih =>
      funext ρ
      change (ops M).denote h ρ >>= (fun z => Empty.elim (M.emptyEquiv z)) = _
      rw [ih]
      rfl
  | iter ha hb iha ihb =>
      funext ρ
      change (ops M).denote ha ρ >>= Elgot.iter (fun x =>
        (ops M).denote hb (ρ, x) >>= fun s => pure (M.coprodEquiv _ _ s)) = _
      rw [iha, ihb]
      rfl

/-- **The bridge for lambda-iter.**  Every lawful monad with an interpretation
of the signature's types and instructions is an algebra of the lambda-case
equational presentation.

Both `coh` and `sound` are discharged: coherence by the coupling theorem of
`Monadic/Coherence.lean`, soundness by `Monadic/Alg.lean`. -/
def _root_.Isotope.LambdaIter.Alg.ofModel (M : Model.{u, v} S m) :
    Alg.{u, v} S where
  toOps := ops M
  coh h k := by
    rw [ops_denote, ops_denote]
    exact funext fun ρ => denote_coh M h k ρ
  sound h k he := by
    rw [ops_denote, ops_denote]
    exact funext fun ρ => sound M he h k ρ


/-- The denotation in `Alg.ofModel` is the monadic denotation. -/
@[simp] theorem ofModel_denote (M : Model.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) :
    (Alg.ofModel M).denote h = denote M h := ops_denote M h

end Monadic
end Isotope.LambdaIter
