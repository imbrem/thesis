import Isotope.LambdaIter.Models.Monadic.Coupling
import Isotope.LambdaIter.Models.Alg
import Isotope.LambdaIter.Metatheory

/-!
# The monadic denotation of lambda-iter

The denotation of an exact lambda-iter typing derivation in a `Monadic.Model`
whose monad carries an iteration operator.  This is the subtyping-free
counterpart of `Isotope/LambdaIter/Subtyping/Semantics/Denotation.lean`, with
the coercion constructor and the free environment removed, since `Alg` fixes
`ν := Empty` and `Γ := Ctx.nil`.

`[Iterate m]` is needed to *state* the `iter` clause; the Elgot laws
(`LawfulElgotMonad`) are needed only for coherence and soundness.
-/

namespace Isotope.LambdaIter

open LocallyNameless

open Isotope.Elgot
open Isotope.LambdaIter.Monadic
open Isotope.LambdaIter.Monadic.SeqModel

universe u v uτ wν qΦ rε

namespace LocallyNameless

variable {τ : Type uτ} [TypeFormers τ]
variable {ν : Type wν} [DecidableEq ν]
variable {Φ : Type qΦ} [HasTy Φ τ]
variable {Γ : LambdaIter.Ctx ν τ}
variable {ε : Type rε} [HasEff Φ ε] {pureEff : ε}

/-- **Regularity**: both endpoints of a lambda-iter equation are typable at its
type.  Typing evidence is `Type`-valued and `Eqv` is a `Prop`, so the
conclusion is necessarily truncated.  Unlike the other two calculi this is
immediate at the axiom rule, since `Eqv.ax` carries both derivations. -/
theorem Eqv.regular {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ} :
    Eqv (Φ := Φ) pureEff Γ β a b A →
      Nonempty (HasType Φ Γ β a A) ∧ Nonempty (HasType Φ Γ β b A) := by
  intro h
  induction h with
  | refl h => exact ⟨⟨h⟩, ⟨h⟩⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | op _ ih => exact ⟨ih.1.map .op, ih.2.map .op⟩
  | let₁ _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.elim fun ha => ih₂.1.elim fun hb => ⟨.let₁ ha hb⟩,
        ih₁.2.elim fun ha => ih₂.2.elim fun hb => ⟨.let₁ ha hb⟩⟩
  | unit => exact ⟨⟨.unit⟩, ⟨.unit⟩⟩
  | pair _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.elim fun ha => ih₂.1.elim fun hb => ⟨.pair ha hb⟩,
        ih₁.2.elim fun ha => ih₂.2.elim fun hb => ⟨.pair ha hb⟩⟩
  | let₂ _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.elim fun ha => ih₂.1.elim fun hb => ⟨.let₂ ha hb⟩,
        ih₁.2.elim fun ha => ih₂.2.elim fun hb => ⟨.let₂ ha hb⟩⟩
  | inl _ ih => exact ⟨ih.1.map .inl, ih.2.map .inl⟩
  | inr _ ih => exact ⟨ih.1.map .inr, ih.2.map .inr⟩
  | case _ _ _ ihe ihl ihr =>
      exact ⟨ihe.1.elim fun he => ihl.1.elim fun hl => ihr.1.elim fun hr =>
          ⟨.case he hl hr⟩,
        ihe.2.elim fun he => ihl.2.elim fun hl => ihr.2.elim fun hr =>
          ⟨.case he hl hr⟩⟩
  | abort _ ih => exact ⟨ih.1.map .abort, ih.2.map .abort⟩
  | iter _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.elim fun ha => ih₂.1.elim fun hb => ⟨.iter ha hb⟩,
        ih₁.2.elim fun ha => ih₂.2.elim fun hb => ⟨.iter ha hb⟩⟩
  | ax _ ha hb => exact ⟨⟨ha⟩, ⟨hb⟩⟩
  | uniformity ha hh _ hb hb' _ =>
      exact ⟨⟨.iter ha hb⟩, ⟨.iter (.let₁ ha hh) hb'⟩⟩

end LocallyNameless

namespace Monadic

variable {S : Sig.{u}} {m : Type v → Type v} [Monad m] [Iterate m]

/-- The denotation of an exact lambda-iter typing derivation.  The
free-variable case is impossible because the free context is empty. -/
def denote (M : Model.{u, v} S m) :
    {n : Nat} → {β : BoundCtx S.Ty n} → {t : Tm Empty S.Instr n} → {A : S.Ty} →
      HasType S.Instr Ctx.nil β t A → M.Env β → m (M.interp A)
  | _, _, _, _, .fv h, _ => absurd h (by simp [Ctx.lookup])
  | _, _, _, _, .bv (ι := i), ρ => pure (Env.get ρ i)
  | _, _, _, _, .op (f := f) ha, ρ => denote M ha ρ >>= M.denoteInstr f
  | _, _, _, _, .let₁ ha hb, ρ => denote M ha ρ >>= fun a => denote M hb (ρ, a)
  | _, _, _, _, .unit, _ => pure (M.unitEquiv.symm ())
  | _, _, _, _, .pair ha hb, ρ =>
      denote M ha ρ >>= fun a => denote M hb ρ >>= fun b =>
        pure ((M.tensorEquiv _ _).symm (a, b))
  | _, _, _, _, .let₂ ha hc, ρ =>
      denote M ha ρ >>= fun ab =>
        denote M hc ((ρ, (M.tensorEquiv _ _ ab).1), (M.tensorEquiv _ _ ab).2)
  | _, _, _, _, .inl ha, ρ =>
      denote M ha ρ >>= fun a => pure ((M.coprodEquiv _ _).symm (.inl a))
  | _, _, _, _, .inr hb, ρ =>
      denote M hb ρ >>= fun b => pure ((M.coprodEquiv _ _).symm (.inr b))
  | _, _, _, _, .case he hl hr, ρ =>
      denote M he ρ >>= fun e =>
        match M.coprodEquiv _ _ e with
        | .inl a => denote M hl (ρ, a)
        | .inr b => denote M hr (ρ, b)
  | _, _, _, _, .abort ha, ρ =>
      denote M ha ρ >>= fun z => Empty.elim (M.emptyEquiv z)
  | _, _, _, _, .iter ha hb, ρ =>
      denote M ha ρ >>= Elgot.iter fun a =>
        denote M hb (ρ, a) >>= fun s => pure (M.coprodEquiv _ _ s)

section Rfl

variable (M : Model.{u, v} S m) {n : Nat} {β : BoundCtx S.Ty n}

@[simp] theorem denote_bv (i : Fin n) (ρ : M.Env β) :
    denote M (.bv (ι := i)) ρ = pure (Env.get ρ i) := rfl

@[simp] theorem denote_op {f : S.Instr} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a (instrSrc f)) (ρ : M.Env β) :
    denote M (.op ha) ρ = denote M ha ρ >>= M.denoteInstr f := rfl

@[simp] theorem denote_let₁ {A B : S.Ty} {a : Tm Empty S.Instr n}
    {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b B) (ρ : M.Env β) :
    denote M (.let₁ ha hb) ρ = denote M ha ρ >>= fun a => denote M hb (ρ, a) :=
  rfl

@[simp] theorem denote_unit (ρ : M.Env β) :
    denote M (β := β) (t := .unit) .unit ρ = pure (M.unitEquiv.symm ()) := rfl

@[simp] theorem denote_pair {A B : S.Ty} {a b : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil β b B) (ρ : M.Env β) :
    denote M (.pair ha hb) ρ =
      denote M ha ρ >>= fun a => denote M hb ρ >>= fun b =>
        pure ((M.tensorEquiv A B).symm (a, b)) := rfl

@[simp] theorem denote_let₂ {A B C : S.Ty} {a : Tm Empty S.Instr n}
    {c : Tm Empty S.Instr (n + 2)}
    (ha : HasType S.Instr Ctx.nil β a (tensor A B))
    (hc : HasType S.Instr Ctx.nil ((β.snoc A).snoc B) c C) (ρ : M.Env β) :
    denote M (.let₂ ha hc) ρ =
      denote M ha ρ >>= fun ab =>
        denote M hc ((ρ, (M.tensorEquiv A B ab).1), (M.tensorEquiv A B ab).2) :=
  rfl

@[simp] theorem denote_inl {A B : S.Ty} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a A) (ρ : M.Env β) :
    denote M (HasType.inl (B := B) ha) ρ =
      denote M ha ρ >>= fun a => pure ((M.coprodEquiv A B).symm (.inl a)) := rfl

@[simp] theorem denote_inr {A B : S.Ty} {b : Tm Empty S.Instr n}
    (hb : HasType S.Instr Ctx.nil β b B) (ρ : M.Env β) :
    denote M (HasType.inr (A := A) hb) ρ =
      denote M hb ρ >>= fun b => pure ((M.coprodEquiv A B).symm (.inr b)) := rfl

@[simp] theorem denote_case {A B C : S.Ty} {e : Tm Empty S.Instr n}
    {l r : Tm Empty S.Instr (n + 1)}
    (he : HasType S.Instr Ctx.nil β e (coprod A B))
    (hl : HasType S.Instr Ctx.nil (β.snoc A) l C)
    (hr : HasType S.Instr Ctx.nil (β.snoc B) r C) (ρ : M.Env β) :
    denote M (.case he hl hr) ρ =
      denote M he ρ >>= fun e =>
        match M.coprodEquiv A B e with
        | .inl a => denote M hl (ρ, a)
        | .inr b => denote M hr (ρ, b) := rfl

@[simp] theorem denote_abort {C : S.Ty} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a empty) (ρ : M.Env β) :
    denote M (HasType.abort (C := C) ha) ρ =
      denote M ha ρ >>= fun z => Empty.elim (M.emptyEquiv z) := rfl

@[simp] theorem denote_iter {A B : S.Ty} {a : Tm Empty S.Instr n}
    {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b (coprod B A)) (ρ : M.Env β) :
    denote M (.iter ha hb) ρ =
      denote M ha ρ >>= Elgot.iter fun a =>
        denote M hb (ρ, a) >>= fun s => pure (M.coprodEquiv B A s) := rfl

end Rfl

section Subst

variable (M : Model.{u, v} S m)

private theorem denote_bv_transport {n : Nat} {β : BoundCtx S.Ty n} (i : Fin n)
    {A : S.Ty} (e : β.get i = A) (ρ : M.Env β) :
    denote M (e ▸ (HasType.bv (Φ := S.Instr) (Γ := Ctx.nil)
      (β := β) (ι := i))) ρ = (pure (e ▸ Env.get ρ i) : m (M.interp A)) := by
  cases e
  rfl

@[simp] theorem denote_newest {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    (ρ : M.Env β) (a : M.interp A) :
    denote M (HasType.newest (Φ := S.Instr) (Γ := Ctx.nil)
      (β := β) (A := A)) (ρ, a) = pure a :=
  denote_bv_transport M (β := .snoc β A) (i := (0 : Fin (n + 1))) rfl (ρ, a)

@[simp] theorem denote_previous {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    (ρ : M.Env β) (a : M.interp A) (b : M.interp B) :
    denote M (HasType.previous (Φ := S.Instr) (Γ := Ctx.nil)
      (β := β) (A := A) (B := B)) ((ρ, a), b) = pure a :=
  denote_bv_transport M (β := .snoc (.snoc β A) B) (i := (1 : Fin (n + 2)))
    rfl ((ρ, a), b)

/-- Denotation is natural under every exactly typed bound renaming. -/
theorem denote_rename {n k : Nat} {β : BoundCtx S.Ty n} {β' : BoundCtx S.Ty k}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) (r : TypedRenaming β β')
    (ρ : M.Env β') :
    denote M (h.rename r) ρ = denote M h (Env.pull r ρ) := by
  induction h generalizing k with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv =>
      refine (denote_bv_transport M (i := r.toFun _) (r.typed _) ρ).trans ?_
      exact congrArg pure (Env.get_pull r ρ _).symm
  | op h ih =>
      simp only [HasType.rename]; unfold denote
      exact congrArg (fun z => z >>= M.denoteInstr _) (ih r ρ)
  | let₁ ha hb iha ihb =>
      simp only [HasType.rename]; unfold denote
      change denote M (ha.rename r) ρ >>=
        (fun a => denote M (hb.rename (r.up _)) (ρ, a)) = _
      rw [iha]
      exact bind_congr fun a => by rw [ihb (r.up _) (ρ, a), Env.pull_up]
  | unit => rfl
  | pair ha hb iha ihb =>
      simp only [HasType.rename]; unfold denote
      rw [iha, ihb]
  | let₂ ha hc iha ihc =>
      simp only [HasType.rename]; unfold denote
      change denote M (ha.rename r) ρ >>= (fun ab =>
        denote M (hc.rename ((r.up _).up _))
          ((ρ, (M.tensorEquiv _ _ ab).1), (M.tensorEquiv _ _ ab).2)) = _
      rw [iha]
      refine bind_congr fun ab => ?_
      rw [ihc ((r.up _).up _) _, Env.pull_up, Env.pull_up]
  | inl h ih =>
      simp only [HasType.rename]; unfold denote
      exact congrArg
        (fun z => z >>= fun a => pure ((M.coprodEquiv _ _).symm (.inl a)))
        (ih r ρ)
  | inr h ih =>
      simp only [HasType.rename]; unfold denote
      exact congrArg
        (fun z => z >>= fun b => pure ((M.coprodEquiv _ _).symm (.inr b)))
        (ih r ρ)
  | case he hl hr ihe ihl ihr =>
      simp only [HasType.rename]; unfold denote
      change denote M (he.rename r) ρ >>= (fun e =>
        match M.coprodEquiv _ _ e with
        | .inl a => denote M (hl.rename (r.up _)) (ρ, a)
        | .inr b => denote M (hr.rename (r.up _)) (ρ, b)) = _
      rw [ihe]
      refine bind_congr fun e => ?_
      cases M.coprodEquiv _ _ e with
      | inl a => simp only; rw [ihl (r.up _) (ρ, a), Env.pull_up]
      | inr b => simp only; rw [ihr (r.up _) (ρ, b), Env.pull_up]
  | abort h ih =>
      simp only [HasType.rename]; unfold denote
      exact congrArg (fun z => z >>= fun y => Empty.elim (M.emptyEquiv y))
        (ih r ρ)
  | iter ha hb iha ihb =>
      simp only [HasType.rename]; unfold denote
      change denote M (ha.rename r) ρ >>= Elgot.iter (fun x =>
        denote M (hb.rename (r.up _)) (ρ, x) >>= fun s =>
          pure (M.coprodEquiv _ _ s)) = _
      rw [iha]
      refine bind_congr fun a => ?_
      congr 1
      funext x
      rw [ihb (r.up _) (ρ, x), Env.pull_up]

@[simp] theorem denote_lift {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A X : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) (ρ : M.Env β)
    (x : M.interp X) :
    denote M (h.lift (B := X)) (ρ, x) = denote M h ρ := by
  have hr := denote_rename M h
    (TypedRenaming.succ β X) (ρ, x)
  rw [Env.pull_succ] at hr
  exact hr

@[simp] theorem denote_underBinder {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr (n + 1)} {A X Y : S.Ty}
    (h : HasType S.Instr Ctx.nil (.snoc β Y) t A) (ρ : M.Env β)
    (x : M.interp X) (y : M.interp Y) :
    denote M (h.underBinder (X := X)) ((ρ, x), y) = denote M h (ρ, y) := by
  have hr := denote_rename M h
    (TypedRenaming.underBinder β X Y) ((ρ, x), y)
  rw [Env.pull_underBinder] at hr
  exact hr

@[simp] theorem denote_underTwoBinders {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr (n + 2)} {A X Y Z : S.Ty}
    (h : HasType S.Instr Ctx.nil ((.snoc (.snoc β Y) Z)) t A)
    (ρ : M.Env β) (x : M.interp X) (y : M.interp Y) (z : M.interp Z) :
    denote M (h.underTwoBinders (X := X)) (((ρ, x), y), z) =
      denote M h ((ρ, y), z) := by
  have hr := denote_rename M h
    (TypedRenaming.underTwoBinders β X Y Z)
    (((ρ, x), y), z)
  rw [Env.pull_underTwoBinders] at hr
  exact hr

/-- A typed substitution *denotes* the values stored in a source environment. -/
def SubstDen {n k : Nat} {β : BoundCtx S.Ty n} {β' : BoundCtx S.Ty k}
    {σ : Fin n → Tm Empty S.Instr k}
    (s : TypedSubst (Γ := Ctx.nil) β β' σ) (ρ' : M.Env β')
    (ρ : M.Env β) : Prop :=
  ∀ i, denote M (s i) ρ' = pure (Env.get ρ i)

theorem SubstDen.up {n k : Nat} {β : BoundCtx S.Ty n} {β' : BoundCtx S.Ty k}
    {σ : Fin n → Tm Empty S.Instr k}
    {s : TypedSubst (Γ := Ctx.nil) β β' σ} {ρ' : M.Env β'}
    {ρ : M.Env β} (hs : SubstDen M s ρ' ρ) (A : S.Ty) (a : M.interp A) :
    SubstDen M (s.up A) (ρ', a) (ρ, a) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change denote M ((s j).lift (B := A)) (ρ', a) = pure (Env.get ρ j)
    rw [denote_lift]
    exact hs j

/-- Semantic substitution for value-respecting simultaneous substitutions. -/
theorem denote_bsubst {n k : Nat} {β : BoundCtx S.Ty n} {β' : BoundCtx S.Ty k}
    {σ : Fin n → Tm Empty S.Instr k}
    (s : TypedSubst (Γ := Ctx.nil) β β' σ)
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) (ρ' : M.Env β')
    (ρ : M.Env β) (hs : SubstDen M s ρ' ρ) :
    denote M (h.bsubst s) ρ' = denote M h ρ := by
  induction h generalizing k with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv => exact hs _
  | op h ih =>
      simp only [HasType.bsubst]; unfold denote
      exact congrArg (fun z => z >>= M.denoteInstr _) (ih s ρ' ρ hs)
  | let₁ ha hb iha ihb =>
      simp only [HasType.bsubst]; unfold denote
      change denote M (ha.bsubst s) ρ' >>=
        (fun a => denote M (hb.bsubst (s.up _)) (ρ', a)) = _
      rw [iha s ρ' ρ hs]
      exact bind_congr fun a =>
        ihb (s.up _) (ρ', a) (ρ, a) (SubstDen.up M hs _ a)
  | unit => rfl
  | pair ha hb iha ihb =>
      simp only [HasType.bsubst]; unfold denote
      rw [iha s ρ' ρ hs, ihb s ρ' ρ hs]
  | let₂ ha hc iha ihc =>
      simp only [HasType.bsubst]; unfold denote
      change denote M (ha.bsubst s) ρ' >>= (fun ab =>
        denote M (hc.bsubst ((s.up _).up _))
          ((ρ', (M.tensorEquiv _ _ ab).1), (M.tensorEquiv _ _ ab).2)) = _
      rw [iha s ρ' ρ hs]
      exact bind_congr fun ab =>
        ihc ((s.up _).up _) _ _
          (SubstDen.up M (SubstDen.up M hs _ _) _ _)
  | inl h ih =>
      simp only [HasType.bsubst]; unfold denote
      exact congrArg
        (fun z => z >>= fun a => pure ((M.coprodEquiv _ _).symm (.inl a)))
        (ih s ρ' ρ hs)
  | inr h ih =>
      simp only [HasType.bsubst]; unfold denote
      exact congrArg
        (fun z => z >>= fun b => pure ((M.coprodEquiv _ _).symm (.inr b)))
        (ih s ρ' ρ hs)
  | case he hl hr ihe ihl ihr =>
      simp only [HasType.bsubst]; unfold denote
      change denote M (he.bsubst s) ρ' >>= (fun e =>
        match M.coprodEquiv _ _ e with
        | .inl a => denote M (hl.bsubst (s.up _)) (ρ', a)
        | .inr b => denote M (hr.bsubst (s.up _)) (ρ', b)) = _
      rw [ihe s ρ' ρ hs]
      refine bind_congr fun e => ?_
      cases M.coprodEquiv _ _ e with
      | inl a => exact ihl (s.up _) (ρ', a) (ρ, a) (SubstDen.up M hs _ a)
      | inr b => exact ihr (s.up _) (ρ', b) (ρ, b) (SubstDen.up M hs _ b)
  | abort h ih =>
      simp only [HasType.bsubst]; unfold denote
      exact congrArg (fun z => z >>= fun y => Empty.elim (M.emptyEquiv y))
        (ih s ρ' ρ hs)
  | iter ha hb iha ihb =>
      simp only [HasType.bsubst]; unfold denote
      change denote M (ha.bsubst s) ρ' >>= Elgot.iter (fun x =>
        denote M (hb.bsubst (s.up _)) (ρ', x) >>= fun t =>
          pure (M.coprodEquiv _ _ t)) = _
      rw [iha s ρ' ρ hs]
      refine bind_congr fun a => ?_
      congr 1
      funext x
      exact congrArg (fun z => z >>= fun t => pure (M.coprodEquiv _ _ t))
        (ihb (s.up _) (ρ', x) (ρ, x) (SubstDen.up M hs _ x))

/-- Opening a binder by a computation that denotes a value agrees with
extending the environment by that value. -/
theorem denote_instantiate {n : Nat} {β : BoundCtx S.Ty n}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)} {A B : S.Ty}
    (hb : HasType S.Instr Ctx.nil (.snoc β A) b B)
    (ha : HasType S.Instr Ctx.nil β a A) (ρ : M.Env β)
    (x : M.interp A) (hx : denote M ha ρ = pure x) :
    denote M (hb.instantiate ha) ρ = denote M hb (ρ, x) := by
  refine denote_bsubst M _ hb ρ (ρ, x) ?_
  intro i
  exact Fin.cases hx (fun _ => rfl) i

/-- Every syntactically pure, well-typed lambda-case term denotes a value. -/
theorem denote_pure_factor [LawfulMonad m] {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty} (hp : Pure S.pureEff t)
    (h : HasType S.Instr Ctx.nil β t A) (ρ : M.Env β) :
    ∃ a : M.interp A, denote M h ρ = (pure a : m (M.interp A)) := by
  induction h with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv => exact ⟨_, rfl⟩
  | op ha ih =>
      cases hp with
      | op hf hpa =>
          obtain ⟨a, ha'⟩ := ih hpa ρ
          exact ⟨M.denotePureInstr _ hf a, by
            rw [denote_op, ha', pure_bind, M.denoteInstr_pure]⟩
  | let₁ ha hb iha ihb =>
      cases hp with
      | let₁ hpa hpb =>
          obtain ⟨a, ha'⟩ := iha hpa ρ
          obtain ⟨b, hb'⟩ := ihb hpb (ρ, a)
          exact ⟨b, by rw [denote_let₁, ha', pure_bind, hb']⟩
  | unit => exact ⟨_, rfl⟩
  | pair ha hb iha ihb =>
      cases hp with
      | pair hpa hpb =>
          obtain ⟨a, ha'⟩ := iha hpa ρ
          obtain ⟨b, hb'⟩ := ihb hpb ρ
          exact ⟨(M.tensorEquiv _ _).symm (a, b), by
            rw [denote_pair, ha', pure_bind, hb', pure_bind]⟩
  | let₂ ha hc iha ihc =>
      cases hp with
      | let₂ hpa hpc =>
          obtain ⟨ab, hab⟩ := iha hpa ρ
          obtain ⟨c, hc'⟩ :=
            ihc hpc ((ρ, (M.tensorEquiv _ _ ab).1), (M.tensorEquiv _ _ ab).2)
          exact ⟨c, by rw [denote_let₂, hab, pure_bind, hc']⟩
  | inl h ih =>
      cases hp with
      | inl hpa =>
          obtain ⟨a, ha'⟩ := ih hpa ρ
          exact ⟨(M.coprodEquiv _ _).symm (.inl a), by
            rw [denote_inl, ha', pure_bind]⟩
  | inr h ih =>
      cases hp with
      | inr hpb =>
          obtain ⟨b, hb'⟩ := ih hpb ρ
          exact ⟨(M.coprodEquiv _ _).symm (.inr b), by
            rw [denote_inr, hb', pure_bind]⟩
  | case he hl hr ihe ihl ihr =>
      cases hp with
      | case hpe hpl hpr =>
          obtain ⟨e, he'⟩ := ihe hpe ρ
          rw [denote_case, he', pure_bind]
          cases hs : M.coprodEquiv _ _ e with
          | inl a =>
              obtain ⟨c, hc⟩ := ihl hpl (ρ, a)
              exact ⟨c, by simpa [hs] using hc⟩
          | inr b =>
              obtain ⟨c, hc⟩ := ihr hpr (ρ, b)
              exact ⟨c, by simpa [hs] using hc⟩
  | abort h ih =>
      cases hp with
      | abort hpa =>
          obtain ⟨z, _⟩ := ih hpa ρ
          exact Empty.elim (M.emptyEquiv z)
  | iter ha hb _ _ => cases hp

end Subst

end Monadic
end Isotope.LambdaIter
