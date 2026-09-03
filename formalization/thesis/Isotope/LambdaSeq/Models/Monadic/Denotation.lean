import Isotope.LambdaIter.Models.Monadic.Model
import Isotope.LambdaSeq.Models.Alg
import Isotope.LambdaSeq.Metatheory.Renaming

/-!
# The monadic denotation of lambda-seq

The denotation of an exact lambda-seq typing derivation in a `SeqModel`: a map
from environments for the bound context to Kleisli computations.  Only
`[Monad m]` and `[LawfulMonad m]` are used — no iteration operator, and no
type former, since lambda-seq has none.

This file also supplies the two pieces of lambda-seq metatheory the bridge
needs and which `Metatheory/Renaming.lean` had not: simultaneous typed
substitution (`TypedSubst`, `HasType.bsubst`, `HasType.instantiate`) and
regularity of the equational theory (`Equiv.regular`).
-/

namespace Isotope.LambdaSeq

open LocallyNameless

open Isotope.LambdaIter (Sig instrSrc instrTrg IsPure)
open Isotope.LambdaIter.Monadic

universe u v uτ wν qΦ rε

namespace LocallyNameless

variable {τ : Type uτ} [LambdaIter.TypeFormers τ]
variable {ν : Type wν} [DecidableEq ν]
variable {Φ : Type qΦ} [LambdaIter.HasTy Φ τ]
variable {Γ : Ctx ν τ}

/-- A simultaneous substitution supplying an exactly typed image for each
bound variable. -/
def TypedSubst (β : BoundCtx τ n) (β' : BoundCtx τ m)
    (σ : Fin n → Tm ν Φ m) : Type (max uτ qΦ wν) :=
  (i : Fin n) → HasType Φ Γ β' (σ i) (β.get i)

namespace TypedSubst

/-- Push a typed substitution under one binder. -/
def up {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) (A : τ) :
    TypedSubst (Γ := Γ) (.snoc β A) (.snoc β' A)
      (fun i => Fin.cases (.bv (0 : Fin (m + 1))) (fun j => (σ j).lift) i) :=
  Fin.cases (.bv) (fun i => (s i).lift)

end TypedSubst

namespace HasType

/-- Typing is preserved by simultaneous bound substitution. -/
def bsubst {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β' (t.bsubst σ) A
  | _, _, .fv h => .fv h
  | _, _, .bv (i := i) => s i
  | _, _, .op h => .op (bsubst s h)
  | _, _, .let₁ ha hb => .let₁ (bsubst s ha) (bsubst (s.up _) hb)

/-- Opening the newest binder preserves typing. -/
def instantiate {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : HasType Φ Γ (.snoc β A) b B) (ha : HasType Φ Γ β a A) :
    HasType Φ Γ β (Tm.instantiate b a) B :=
  bsubst (σ := Fin.cases a fun i => .bv i) (Fin.cases ha fun _ => .bv) hb

end HasType

variable {ε : Type rε} [LambdaIter.HasEff Φ ε] {pureEff : ε}

/-- **Regularity**: both endpoints of a lambda-seq equation are typable at its
type.  Typing evidence is `Type`-valued and `Equiv` is a `Prop`, so the
conclusion is necessarily truncated. -/
theorem Equiv.regular {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ} :
    Equiv (Φ := Φ) pureEff Γ β a b A →
      Nonempty (HasType Φ Γ β a A) ∧ Nonempty (HasType Φ Γ β b A) := by
  intro h
  induction h with
  | var h => exact ⟨⟨.fv h⟩, ⟨.fv h⟩⟩
  | bvar => exact ⟨⟨.bv⟩, ⟨.bv⟩⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | op _ ih => exact ⟨ih.1.map .op, ih.2.map .op⟩
  | let₁ _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.elim fun ha => ih₂.1.elim fun hb => ⟨.let₁ ha hb⟩,
        ih₁.2.elim fun ha => ih₂.2.elim fun hb => ⟨.let₁ ha hb⟩⟩
  | letBeta hp ha hb => exact ⟨⟨.let₁ ha hb⟩, ⟨hb.instantiate ha⟩⟩
  | letEta ha => exact ⟨⟨.let₁ ha .bv⟩, ⟨ha⟩⟩
  | bindOp ha hc =>
      exact ⟨⟨.let₁ (.op ha) hc⟩, ⟨.let₁ ha (.let₁ (.op .bv) hc.underBinder)⟩⟩
  | bindLet ha hb hc =>
      exact ⟨⟨.let₁ (.let₁ ha hb) hc⟩, ⟨.let₁ ha (.let₁ hb hc.underBinder)⟩⟩

end LocallyNameless

namespace Monadic

open Isotope.LambdaIter.Monadic.SeqModel

variable {S : Sig.{u}} {m : Type v → Type v} [Monad m]

/-- The denotation of an exact lambda-seq typing derivation.  The free-variable
case is impossible because the free context is empty. -/
def denote (M : SeqModel.{u, v} S m) :
    {n : Nat} → {β : BoundCtx S.Ty n} → {t : Tm Empty S.Instr n} → {A : S.Ty} →
      HasType S.Instr LambdaIter.Ctx.nil β t A → M.Env β → m (M.interp A)
  | _, _, _, _, .fv h, _ => absurd h (by simp [LambdaIter.Ctx.lookup])
  | _, _, _, _, .bv (i := i), ρ => pure (Env.get ρ i)
  | _, _, _, _, .op (f := f) ha, ρ => denote M ha ρ >>= M.denoteInstr f
  | _, _, _, _, .let₁ ha hb, ρ => denote M ha ρ >>= fun a => denote M hb (ρ, a)

@[simp] theorem denote_bv (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} (i : Fin n) (ρ : M.Env β) :
    denote M (.bv (i := i)) ρ = pure (Env.get ρ i) := rfl

@[simp] theorem denote_op (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {f : S.Instr} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a (instrSrc f)) (ρ : M.Env β) :
    denote M (.op ha) ρ = denote M ha ρ >>= M.denoteInstr f := rfl

@[simp] theorem denote_let₁ (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {A B : S.Ty} {a : Tm Empty S.Instr n}
    {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a A)
    (hb : HasType S.Instr LambdaIter.Ctx.nil (β.snoc A) b B) (ρ : M.Env β) :
    denote M (.let₁ ha hb) ρ = denote M ha ρ >>= fun a => denote M hb (ρ, a) :=
  rfl


private theorem denote_bv_transport (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} (i : Fin n) {A : S.Ty} (e : β.get i = A)
    (ρ : M.Env β) :
    denote M (e ▸ (HasType.bv (Φ := S.Instr) (Γ := LambdaIter.Ctx.nil)
      (β := β) (i := i))) ρ = (pure (e ▸ Env.get ρ i) : m (M.interp A)) := by
  cases e
  rfl

@[simp] theorem denote_newest (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} (ρ : M.Env β) (a : M.interp A) :
    denote M (HasType.newest (Φ := S.Instr) (Γ := LambdaIter.Ctx.nil)
      (β := β) (A := A)) (ρ, a) = pure a :=
  denote_bv_transport M (β := .snoc β A) (i := (0 : Fin (n + 1))) rfl (ρ, a)

/-- Denotation is natural under every exactly typed bound renaming. -/
theorem denote_rename (M : SeqModel.{u, v} S m) {n k : Nat}
    {β : BoundCtx S.Ty n} {β' : BoundCtx S.Ty k} {t : Tm Empty S.Instr n}
    {A : S.Ty} (h : HasType S.Instr LambdaIter.Ctx.nil β t A)
    (r : LambdaIter.LocallyNameless.TypedRenaming β β') (ρ : M.Env β') :
    denote M (h.rename r) ρ = denote M h (Env.pull r ρ) := by
  induction h generalizing k with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv =>
      refine (denote_bv_transport M (i := r.toFun _) (r.typed _) ρ).trans ?_
      exact congrArg pure (Env.get_pull r ρ _).symm
  | op h ih => exact congrArg (fun z => z >>= M.denoteInstr _) (ih r ρ)
  | let₁ ha hb iha ihb =>
      show denote M (ha.rename r) ρ >>=
          (fun a => denote M (hb.rename (r.up _)) (ρ, a)) =
        denote M ha (Env.pull r ρ) >>= (fun a => denote M hb (Env.pull r ρ, a))
      rw [iha]
      exact bind_congr fun a => by rw [ihb (r.up _) (ρ, a), Env.pull_up]

@[simp] theorem denote_lift (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A X : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) (ρ : M.Env β)
    (x : M.interp X) :
    denote M (h.lift (B := X)) (ρ, x) = denote M h ρ := by
  have hr := denote_rename M h
    (LambdaIter.LocallyNameless.TypedRenaming.succ β X) (ρ, x)
  rw [Env.pull_succ] at hr
  exact hr

@[simp] theorem denote_underBinder (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr (n + 1)} {A X Y : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil (.snoc β Y) t A) (ρ : M.Env β)
    (x : M.interp X) (y : M.interp Y) :
    denote M (h.underBinder (X := X)) ((ρ, x), y) = denote M h (ρ, y) := by
  have hr := denote_rename M h
    (LambdaIter.LocallyNameless.TypedRenaming.underBinder β X Y) ((ρ, x), y)
  rw [Env.pull_underBinder] at hr
  exact hr

/-- A typed substitution *denotes* the values stored in a source environment. -/
def SubstDen (M : SeqModel.{u, v} S m) {n k : Nat} {β : BoundCtx S.Ty n}
    {β' : BoundCtx S.Ty k} {σ : Fin n → Tm Empty S.Instr k}
    (s : TypedSubst (Γ := LambdaIter.Ctx.nil) β β' σ) (ρ' : M.Env β')
    (ρ : M.Env β) : Prop :=
  ∀ i, denote M (s i) ρ' = pure (Env.get ρ i)

theorem SubstDen.up {M : SeqModel.{u, v} S m} {n k : Nat}
    {β : BoundCtx S.Ty n} {β' : BoundCtx S.Ty k}
    {σ : Fin n → Tm Empty S.Instr k}
    {s : TypedSubst (Γ := LambdaIter.Ctx.nil) β β' σ} {ρ' : M.Env β'}
    {ρ : M.Env β} (hs : SubstDen M s ρ' ρ) (A : S.Ty) (a : M.interp A) :
    SubstDen M (s.up A) (ρ', a) (ρ, a) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · show denote M ((s j).lift (B := A)) (ρ', a) = pure (Env.get ρ j)
    rw [denote_lift]
    exact hs j

/-- Semantic substitution for value-respecting simultaneous substitutions. -/
theorem denote_bsubst (M : SeqModel.{u, v} S m) {n k : Nat}
    {β : BoundCtx S.Ty n} {β' : BoundCtx S.Ty k}
    {σ : Fin n → Tm Empty S.Instr k}
    (s : TypedSubst (Γ := LambdaIter.Ctx.nil) β β' σ)
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) (ρ' : M.Env β')
    (ρ : M.Env β) (hs : SubstDen M s ρ' ρ) :
    denote M (h.bsubst s) ρ' = denote M h ρ := by
  induction h generalizing k with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv => simpa only [HasType.bsubst, denote_bv] using hs _
  | op h ih =>
      exact congrArg (fun z => z >>= M.denoteInstr _) (ih s ρ' ρ hs)
  | let₁ ha hb iha ihb =>
      show denote M (ha.bsubst s) ρ' >>=
          (fun a => denote M (hb.bsubst (s.up _)) (ρ', a)) =
        denote M ha ρ >>= (fun a => denote M hb (ρ, a))
      rw [iha s ρ' ρ hs]
      exact bind_congr fun a => ihb (s.up _) (ρ', a) (ρ, a) (hs.up _ a)

/-- Opening a binder by a computation that denotes a value agrees with
extending the environment by that value. -/
theorem denote_instantiate (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    {A B : S.Ty} (hb : HasType S.Instr LambdaIter.Ctx.nil (.snoc β A) b B)
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a A) (ρ : M.Env β)
    (x : M.interp A) (hx : denote M ha ρ = pure x) :
    denote M (hb.instantiate ha) ρ = denote M hb (ρ, x) := by
  refine denote_bsubst M _ hb ρ (ρ, x) ?_
  intro i
  exact Fin.cases hx (fun _ => rfl) i

/-- Every syntactically pure, well-typed lambda-seq term denotes a value. -/
theorem denote_pure_factor [LawfulMonad m] (M : SeqModel.{u, v} S m) {n : Nat}
    {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (hp : Pure S.pureEff t)
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) (ρ : M.Env β) :
    ∃ a : M.interp A, denote M h ρ = (pure a : m (M.interp A)) := by
  induction h with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv => exact ⟨_, rfl⟩
  | op ha ih =>
      cases hp with
      | op hf hpa =>
          obtain ⟨a, ha'⟩ := ih hpa ρ
          refine ⟨M.denotePureInstr _ hf a, ?_⟩
          rw [denote_op, ha', pure_bind, M.denoteInstr_pure]
  | let₁ ha hb iha ihb =>
      cases hp with
      | let₁ hpa hpb =>
          obtain ⟨a, ha'⟩ := iha hpa ρ
          obtain ⟨b, hb'⟩ := ihb hpb (ρ, a)
          exact ⟨b, by rw [denote_let₁, ha', pure_bind, hb']⟩

end Monadic
end Isotope.LambdaSeq
