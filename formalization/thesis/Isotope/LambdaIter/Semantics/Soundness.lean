import Isotope.LambdaIter.Semantics.Substitution
import Isotope.LambdaIter.LocallyNameless.TypedEquiv

/-! # Soundness of the typed lambda-iter equations -/

namespace Isotope.LambdaIter.Semantics

open Isotope.Elgot
open Isotope.LambdaIter.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m]
variable [InstructionModel Φ τ ε m]

theorem sound_letBeta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (hp : Pure (⊥ : ε) a) (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b B) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ ha hb) γ ρ =
      denote (m := m) (ε := ε) (hb.instantiate ha) γ ρ := by
  rcases denote_pure_factor (m := m) (ε := ε) hp ha γ ρ with ⟨x, hx⟩
  simp only [denote, hx, LawfulMonad.pure_bind]
  exact (denote_instantiate (m := m) (ε := ε) hb ha γ ρ x hx).symm

theorem sound_letEta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A : τ} (ha : HasType Φ Γ β a A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ ha HasType.newest) γ ρ =
      denote (m := m) (ε := ε) ha γ ρ := by
  simp [denote]

theorem sound_unitEta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} (ha : HasType Φ Γ β a TypeFormers.unit)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ ha .unit) γ ρ =
      denote (m := m) (ε := ε) ha γ ρ := by
  simp only [denote]
  calc
    _ = denote (m := m) (ε := ε) ha γ ρ >>= pure := by
      apply bind_congr
      intro x
      congr 1
      exact TypeModel.unitEquiv.injective (Subsingleton.elim _ _)
    _ = _ := bind_pure _

theorem sound_pairEta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A B : τ}
    (ha : HasType Φ Γ β a (TypeFormers.tensor A B))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε)
        (.let₂ ha (.pair HasType.previous HasType.newest)) γ ρ =
      denote (m := m) (ε := ε) ha γ ρ := by
  simp [denote]
  rfl

theorem sound_caseEta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {A B : τ}
    (he : HasType Φ Γ β e (TypeFormers.coprod A B))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε)
        (.case he (.inl HasType.newest) (.inr HasType.newest)) γ ρ =
      denote (m := m) (ε := ε) he γ ρ := by
  simp only [denote]
  rw [← bind_pure (denote (m := m) (ε := ε) he γ ρ)]
  apply bind_congr
  intro e
  cases hs : TypeModel.coprodEquiv A B e with
  | inl a =>
      simp only [denote_newest, LawfulMonad.pure_bind]
      congr 1
      simpa [hs] using (TypeModel.coprodEquiv A B).symm_apply_apply e
  | inr b =>
      simp only [denote_newest, LawfulMonad.pure_bind]
      congr 1
      simpa [hs] using (TypeModel.coprodEquiv A B).symm_apply_apply e

theorem sound_pairBeta {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
    (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₂ (.pair ha hb) hc) γ ρ =
      denote (m := m) (ε := ε) (.let₁ ha (.let₁ (hb.lift (B := A)) hc)) γ ρ := by
  simp only [denote, LawfulMonad.bind_assoc]
  apply bind_congr
  intro x
  rw [denote_lift]
  apply bind_congr
  intro y
  simp

theorem sound_caseBetaL {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l : Tm ν Φ (n + 1)} {r : Tm ν Φ (n + 1)} {A B C : τ}
    (he : HasType Φ Γ β e A) (hl : HasType Φ Γ (.snoc β A) l C)
    (hr : HasType Φ Γ (.snoc β B) r C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.case (.inl he) hl hr) γ ρ =
      denote (m := m) (ε := ε) (.let₁ he hl) γ ρ := by
  simp [denote]

theorem sound_caseBetaR {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l : Tm ν Φ (n + 1)} {r : Tm ν Φ (n + 1)} {A B C : τ}
    (he : HasType Φ Γ β e B) (hl : HasType Φ Γ (.snoc β A) l C)
    (hr : HasType Φ Γ (.snoc β B) r C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.case (.inr he) hl hr) γ ρ =
      denote (m := m) (ε := ε) (.let₁ he hr) γ ρ := by
  simp [denote]

theorem sound_bindOp {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {c : Tm ν Φ (n + 1)} {C : τ} {f : Φ}
    (ha : HasType Φ Γ β a (instrSrc f))
    (hc : HasType Φ Γ (.snoc β (instrTrg f)) c C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ (.op ha) hc) γ ρ =
      denote (m := m) (ε := ε)
        (.let₁ ha (.let₁ (.op HasType.newest) hc.underBinder)) γ ρ := by
  simp only [denote, denote_newest, denote_underBinder, LawfulMonad.pure_bind]
  simp only [LawfulMonad.bind_assoc]

theorem sound_bindLet {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A B C : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B)
    (hc : HasType Φ Γ (.snoc β B) c C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ (.let₁ ha hb) hc) γ ρ =
      denote (m := m) (ε := ε) (.let₁ ha (.let₁ hb hc.underBinder)) γ ρ := by
  simp only [denote, denote_underBinder]
  simp only [LawfulMonad.bind_assoc]

theorem sound_bindLetPair {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {d : Tm ν Φ (n + 1)}
    {A B C D : τ}
    (he : HasType Φ Γ β e (TypeFormers.tensor A B))
    (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
    (hd : HasType Φ Γ (.snoc β C) d D)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ (.let₂ he hc) hd) γ ρ =
      denote (m := m) (ε := ε)
        (.let₂ he (.let₁ hc (hd.underBinder.underBinder))) γ ρ := by
  simp only [denote, denote_underBinder, LawfulMonad.bind_assoc]

theorem sound_bindLetCase {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r d : Tm ν Φ (n + 1)} {A B C D : τ}
    (he : HasType Φ Γ β e (TypeFormers.coprod A B))
    (hl : HasType Φ Γ (.snoc β A) l C)
    (hr : HasType Φ Γ (.snoc β B) r C)
    (hd : HasType Φ Γ (.snoc β C) d D)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ (.case he hl hr) hd) γ ρ =
      denote (m := m) (ε := ε)
        (.case he (.let₁ hl hd.underBinder) (.let₁ hr hd.underBinder)) γ ρ := by
  simp only [denote, denote_underBinder, LawfulMonad.bind_assoc]
  apply bind_congr
  intro e
  cases TypeModel.coprodEquiv A B e <;> rfl

theorem sound_bindPair {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
    (ha : HasType Φ Γ β a (TypeFormers.tensor A B))
    (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₂ ha hc) γ ρ =
      denote (m := m) (ε := ε)
        (.let₁ ha (.let₂ HasType.newest hc.underTwoBinders)) γ ρ := by
  simp only [denote, denote_underTwoBinders]
  apply bind_congr
  intro ab
  have hn : denote (m := m) (ε := ε)
      (HasType.newest (Φ := Φ) (Γ := Γ) (β := β)
        (A := TypeFormers.tensor A B)) γ (ρ, ab) = pure ab :=
    denote_newest (m := m) (ε := ε) γ ρ ab
  let k := fun ab : TyDen (TypeFormers.tensor A B) =>
    denote (m := m) (ε := ε) hc γ
      ((ρ, (TypeModel.tensorEquiv A B ab).1),
        (TypeModel.tensorEquiv A B ab).2)
  calc
    _ = (pure ab : m _) >>= k := (LawfulMonad.pure_bind ab k).symm
    _ = denote (m := m) (ε := ε)
          (HasType.newest (Φ := Φ) (Γ := Γ) (β := β)
            (A := TypeFormers.tensor A B)) γ (ρ, ab) >>= k :=
      congrArg (fun x => x >>= k) hn.symm
    _ = _ := rfl

theorem sound_bindCase {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
    (he : HasType Φ Γ β e (TypeFormers.coprod A B))
    (hl : HasType Φ Γ (.snoc β A) l C)
    (hr : HasType Φ Γ (.snoc β B) r C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.case he hl hr) γ ρ =
      denote (m := m) (ε := ε)
        (.let₁ he (.case HasType.newest hl.underBinder hr.underBinder)) γ ρ := by
  simp only [denote, denote_underBinder]
  apply bind_congr
  intro e
  have hn : denote (m := m) (ε := ε)
      (HasType.newest (Φ := Φ) (Γ := Γ) (β := β)
        (A := TypeFormers.coprod A B)) γ (ρ, e) = pure e :=
    denote_newest (m := m) (ε := ε) γ ρ e
  let k := fun e : TyDen (TypeFormers.coprod A B) =>
    match TypeModel.coprodEquiv A B e with
    | .inl a => denote (m := m) (ε := ε) hl γ (ρ, a)
    | .inr b => denote (m := m) (ε := ε) hr γ (ρ, b)
  calc
    _ = (pure e : m _) >>= k := (LawfulMonad.pure_bind e k).symm
    _ = denote (m := m) (ε := ε)
          (HasType.newest (Φ := Φ) (Γ := Γ) (β := β)
            (A := TypeFormers.coprod A B)) γ (ρ, e) >>= k :=
      congrArg (fun x => x >>= k) hn.symm
    _ = _ := rfl

theorem sound_emptyInitial {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a TypeFormers.empty)
    (hb : HasType Φ Γ (.snoc β A) b B)
    (hc : HasType Φ Γ (.snoc β A) c B)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ (.abort ha) hb) γ ρ =
      denote (m := m) (ε := ε) (.let₁ (.abort ha) hc) γ ρ := by
  simp only [denote, LawfulMonad.bind_assoc]
  apply bind_congr
  intro z
  exact (TypeModel.emptyEquiv z).elim

end Isotope.LambdaIter.Semantics
