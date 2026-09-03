import Isotope.LambdaCase.Models.Monadic.Coherence

/-!
# Every monad gives an algebra of the lambda-case presentation

This closes, for lambda-case, the gap recorded in `Models/Alg.lean`: both
propositional fields of `Alg` are discharged for the monadic denotation.
`coh` is `Monadic/Coherence.lean`; `sound` is proved here, one lemma per
axiom of `Equiv`, and the congruence cases go by replacing both given
derivations with canonical ones built from the equation's own data.

## Hypotheses

`[Monad m]`, `[LawfulMonad m]`, and `[InjectiveFormers S.Ty]`.  No iteration
operator and no Elgot law: lambda-case is the iteration-free fragment, and its
bridge must not (and does not) need them.
-/

namespace Isotope.LambdaCase.Monadic

open LocallyNameless

open Isotope.LambdaIter (Sig instrSrc instrTrg TypeFormers InjectiveFormers)
open Isotope.LambdaIter.Monadic
open Isotope.LambdaIter.Monadic.SeqModel

universe u v

variable {S : Sig.{u}} {m : Type v → Type v} [Monad m] [LawfulMonad m]

section Axioms

variable (M : Model.{u, v} S m) {n : Nat} {β : BoundCtx S.Ty n}

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

/-- Soundness of the eta law for the unit type. -/
theorem sound_unitEta {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a TypeFormers.unit)
    (ρ : M.Env β) :
    denote M (.let₁ ha .unit) ρ = denote M ha ρ := by
  rw [denote_let₁]
  calc
    _ = denote M ha ρ >>= pure := by
        refine bind_congr fun x => ?_
        exact congrArg (fun z => (Pure.pure z : m (M.interp TypeFormers.unit)))
          (M.unitEquiv.injective (Subsingleton.elim _ _))
    _ = _ := bind_pure _

/-- Soundness of the beta law for pairs. -/
theorem sound_pairBeta {a b : Tm Empty S.Instr n} {c : Tm Empty S.Instr (n + 2)}
    {A B C : S.Ty} (ha : HasType S.Instr LambdaIter.Ctx.nil β a A)
    (hb : HasType S.Instr LambdaIter.Ctx.nil β b B)
    (hc : HasType S.Instr LambdaIter.Ctx.nil ((β.snoc A).snoc B) c C)
    (ρ : M.Env β) :
    denote M (.let₂ (.pair ha hb) hc) ρ =
      denote M (.let₁ ha (.let₁ (hb.lift (B := A)) hc)) ρ := by
  simp only [denote_let₂, denote_pair, denote_let₁, bind_assoc]
  refine bind_congr fun x => ?_
  rw [denote_lift]
  refine bind_congr fun y => ?_
  rw [pure_bind]
  simp

/-- Soundness of the eta law for pairs. -/
theorem sound_pairEta {a : Tm Empty S.Instr n} {A B : S.Ty}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a (TypeFormers.tensor A B))
    (ρ : M.Env β) :
    denote M (.let₂ ha (.pair HasType.previous HasType.newest)) ρ =
      denote M ha ρ := by
  simp only [denote_let₂, denote_pair, denote_previous, denote_newest,
    pure_bind]
  calc
    _ = denote M ha ρ >>= pure :=
      bind_congr fun ab => by simp
    _ = _ := bind_pure _

/-- Soundness of the left beta law for `case`. -/
theorem sound_caseBetaL {e : Tm Empty S.Instr n} {l r : Tm Empty S.Instr (n + 1)}
    {A B C : S.Ty} (he : HasType S.Instr LambdaIter.Ctx.nil β e A)
    (hl : HasType S.Instr LambdaIter.Ctx.nil (.snoc β A) l C)
    (hr : HasType S.Instr LambdaIter.Ctx.nil (.snoc β B) r C) (ρ : M.Env β) :
    denote M (.case (.inl (B := B) he) hl hr) ρ = denote M (.let₁ he hl) ρ := by
  simp only [denote_case, denote_inl, denote_let₁, bind_assoc, pure_bind]
  exact bind_congr fun x => by rw [Equiv.apply_symm_apply]

/-- Soundness of the right beta law for `case`. -/
theorem sound_caseBetaR {e : Tm Empty S.Instr n} {l r : Tm Empty S.Instr (n + 1)}
    {A B C : S.Ty} (he : HasType S.Instr LambdaIter.Ctx.nil β e B)
    (hl : HasType S.Instr LambdaIter.Ctx.nil (.snoc β A) l C)
    (hr : HasType S.Instr LambdaIter.Ctx.nil (.snoc β B) r C) (ρ : M.Env β) :
    denote M (.case (.inr (A := A) he) hl hr) ρ = denote M (.let₁ he hr) ρ := by
  simp only [denote_case, denote_inr, denote_let₁, bind_assoc, pure_bind]
  exact bind_congr fun x => by rw [Equiv.apply_symm_apply]

/-- Soundness of the eta law for `case`. -/
theorem sound_caseEta {e : Tm Empty S.Instr n} {A B : S.Ty}
    (he : HasType S.Instr LambdaIter.Ctx.nil β e (TypeFormers.coprod A B))
    (ρ : M.Env β) :
    denote M (.case he (.inl HasType.newest) (.inr HasType.newest)) ρ =
      denote M he ρ := by
  calc
    _ = denote M he ρ >>= pure := by
        rw [denote_case]
        refine bind_congr fun x => ?_
        cases hs : M.coprodEquiv A B x with
        | inl a =>
            simp only [denote_inl, denote_newest, pure_bind]
            exact congrArg (fun z => (Pure.pure z : m (M.interp _)))
              (by simpa [hs] using (M.coprodEquiv A B).symm_apply_apply x)
        | inr b =>
            simp only [denote_inr, denote_newest, pure_bind]
            exact congrArg (fun z => (Pure.pure z : m (M.interp _)))
              (by simpa [hs] using (M.coprodEquiv A B).symm_apply_apply x)
    _ = _ := bind_pure _

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

/-- Soundness of the commuting conversion for a `let` over a pair split. -/
theorem sound_bindLetPair {e : Tm Empty S.Instr n} {c : Tm Empty S.Instr (n + 2)}
    {d : Tm Empty S.Instr (n + 1)} {A B C D : S.Ty}
    (he : HasType S.Instr LambdaIter.Ctx.nil β e (TypeFormers.tensor A B))
    (hc : HasType S.Instr LambdaIter.Ctx.nil ((β.snoc A).snoc B) c C)
    (hd : HasType S.Instr LambdaIter.Ctx.nil (.snoc β C) d D) (ρ : M.Env β) :
    denote M (.let₁ (.let₂ he hc) hd) ρ =
      denote M (.let₂ he (.let₁ hc (hd.underBinder.underBinder))) ρ := by
  simp only [denote_let₁, denote_let₂, bind_assoc, denote_underBinder]

/-- Soundness of the commuting conversion for a `let` over a `case`. -/
theorem sound_bindLetCase {e : Tm Empty S.Instr n}
    {l r d : Tm Empty S.Instr (n + 1)} {A B C D : S.Ty}
    (he : HasType S.Instr LambdaIter.Ctx.nil β e (TypeFormers.coprod A B))
    (hl : HasType S.Instr LambdaIter.Ctx.nil (.snoc β A) l C)
    (hr : HasType S.Instr LambdaIter.Ctx.nil (.snoc β B) r C)
    (hd : HasType S.Instr LambdaIter.Ctx.nil (.snoc β C) d D) (ρ : M.Env β) :
    denote M (.let₁ (.case he hl hr) hd) ρ =
      denote M (.case he (.let₁ hl hd.underBinder) (.let₁ hr hd.underBinder))
        ρ := by
  simp only [denote_let₁, denote_case, bind_assoc, denote_underBinder]
  refine bind_congr fun x => ?_
  cases M.coprodEquiv A B x <;> rfl

/-- Soundness of the law naming the scrutinee of a pair split. -/
theorem sound_bindPair {a : Tm Empty S.Instr n} {c : Tm Empty S.Instr (n + 2)}
    {A B C : S.Ty}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a (TypeFormers.tensor A B))
    (hc : HasType S.Instr LambdaIter.Ctx.nil ((β.snoc A).snoc B) c C)
    (ρ : M.Env β) :
    denote M (.let₂ ha hc) ρ =
      denote M (.let₁ ha (.let₂ HasType.newest hc.underTwoBinders)) ρ := by
  simp only [denote_let₁, denote_let₂, denote_newest, pure_bind,
    denote_underTwoBinders]

/-- Soundness of the law naming the scrutinee of a `case`. -/
theorem sound_bindCase {e : Tm Empty S.Instr n} {l r : Tm Empty S.Instr (n + 1)}
    {A B C : S.Ty}
    (he : HasType S.Instr LambdaIter.Ctx.nil β e (TypeFormers.coprod A B))
    (hl : HasType S.Instr LambdaIter.Ctx.nil (.snoc β A) l C)
    (hr : HasType S.Instr LambdaIter.Ctx.nil (.snoc β B) r C) (ρ : M.Env β) :
    denote M (.case he hl hr) ρ =
      denote M (.let₁ he (.case HasType.newest hl.underBinder hr.underBinder))
        ρ := by
  simp only [denote_let₁, denote_case, denote_newest, pure_bind,
    denote_underBinder]

/-- Soundness of the initiality law for the empty type. -/
theorem sound_emptyInitial {a : Tm Empty S.Instr n}
    {b c : Tm Empty S.Instr (n + 1)} {A B : S.Ty}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a TypeFormers.empty)
    (hb : HasType S.Instr LambdaIter.Ctx.nil (.snoc β A) b B)
    (hc : HasType S.Instr LambdaIter.Ctx.nil (.snoc β A) c B) (ρ : M.Env β) :
    denote M (.let₁ (.abort ha) hb) ρ = denote M (.let₁ (.abort ha) hc) ρ := by
  simp only [denote_let₁, denote_abort, bind_assoc]
  exact bind_congr fun z => (M.emptyEquiv z).elim

end Axioms

variable [InjectiveFormers S.Ty]

/-- **Soundness**: the monadic denotation respects the lambda-case equational
theory.  Every case first rewrites the two given derivations to canonical ones
built from the equation's own data, using coherence. -/
theorem sound (M : Model.{u, v} S m) {n : Nat} {β : BoundCtx S.Ty n}
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
  | letBeta hp ha hb =>
      intro h k ρ
      rw [denote_coh M h (.let₁ ha hb) ρ, denote_coh M k (hb.instantiate ha) ρ]
      exact sound_letBeta M hp ha hb ρ
  | letEta ha =>
      intro h k ρ
      rw [denote_coh M h (.let₁ ha HasType.newest) ρ, denote_coh M k ha ρ]
      exact sound_letEta M ha ρ
  | unitEta ha =>
      intro h k ρ
      rw [denote_coh M h (.let₁ ha .unit) ρ, denote_coh M k ha ρ]
      exact sound_unitEta M ha ρ
  | pairBeta ha hb hc =>
      intro h k ρ
      rw [denote_coh M h (.let₂ (.pair ha hb) hc) ρ,
        denote_coh M k (.let₁ ha (.let₁ hb.lift hc)) ρ]
      exact sound_pairBeta M ha hb hc ρ
  | pairEta ha =>
      intro h k ρ
      rw [denote_coh M h (.let₂ ha (.pair HasType.previous HasType.newest)) ρ,
        denote_coh M k ha ρ]
      exact sound_pairEta M ha ρ
  | caseBetaL he hl hr =>
      intro h k ρ
      rw [denote_coh M h (.case (.inl he) hl hr) ρ,
        denote_coh M k (.let₁ he hl) ρ]
      exact sound_caseBetaL M he hl hr ρ
  | caseBetaR he hl hr =>
      intro h k ρ
      rw [denote_coh M h (.case (.inr he) hl hr) ρ,
        denote_coh M k (.let₁ he hr) ρ]
      exact sound_caseBetaR M he hl hr ρ
  | caseEta he =>
      intro h k ρ
      rw [denote_coh M h
          (.case he (.inl HasType.newest) (.inr HasType.newest)) ρ,
        denote_coh M k he ρ]
      exact sound_caseEta M he ρ
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
  | bindLetPair he hc hd =>
      intro h k ρ
      rw [denote_coh M h (.let₁ (.let₂ he hc) hd) ρ,
        denote_coh M k (.let₂ he (.let₁ hc hd.underBinder.underBinder)) ρ]
      exact sound_bindLetPair M he hc hd ρ
  | bindLetCase he hl hr hd =>
      intro h k ρ
      rw [denote_coh M h (.let₁ (.case he hl hr) hd) ρ,
        denote_coh M k
          (.case he (.let₁ hl hd.underBinder) (.let₁ hr hd.underBinder)) ρ]
      exact sound_bindLetCase M he hl hr hd ρ
  | bindPair ha hc =>
      intro h k ρ
      rw [denote_coh M h (.let₂ ha hc) ρ,
        denote_coh M k (.let₁ ha (.let₂ HasType.newest hc.underTwoBinders)) ρ]
      exact sound_bindPair M ha hc ρ
  | bindCase he hl hr =>
      intro h k ρ
      rw [denote_coh M h (.case he hl hr) ρ,
        denote_coh M k
          (.let₁ he (.case HasType.newest hl.underBinder hr.underBinder)) ρ]
      exact sound_bindCase M he hl hr ρ
  | emptyInitial ha hb hc =>
      intro h k ρ
      rw [denote_coh M h (.let₁ (.abort ha) hb) ρ,
        denote_coh M k (.let₁ (.abort ha) hc) ρ]
      exact sound_emptyInitial M ha hb hc ρ

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

/-- The interpretation of a derivation by `ops` is the monadic denotation. -/
@[simp] theorem ops_denote (M : Model.{u, v} S m) {n : Nat}
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

/-- **The bridge for lambda-case.**  Every lawful monad with an interpretation
of the signature's types and instructions is an algebra of the lambda-case
equational presentation.

No iteration operator and no Elgot law is used. -/
def _root_.Isotope.LambdaCase.Alg.ofModel (M : Model.{u, v} S m) :
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
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    (Alg.ofModel M).denote h = denote M h := ops_denote M h

end Isotope.LambdaCase.Monadic
