import Isotope.LambdaIter.Subtyping.Semantics.Substitution
import Isotope.LambdaIter.Subtyping.LocallyNameless.TypedEquiv

/-! # Soundness of the typed lambda-iter equations -/

namespace Isotope.LambdaIter.Subtyping.Semantics

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

theorem sound_iterBind {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.iter ha hb) γ ρ =
      denote (m := m) (ε := ε)
        (.let₁ ha (.iter HasType.newest hb.underBinder)) γ ρ := by
  simp only [denote, denote_underBinder]
  apply bind_congr
  intro a
  have hn : denote (m := m) (ε := ε)
      (HasType.newest (Φ := Φ) (Γ := Γ) (β := β) (A := A)) γ (ρ, a) = pure a :=
    denote_newest (m := m) (ε := ε) γ ρ a
  let body := fun x : TyDen A =>
    denote (m := m) (ε := ε) hb γ (ρ, x) >>= fun s =>
      pure (TypeModel.coprodEquiv B A s)
  calc
    Elgot.iter body a = (pure a : m _) >>= Elgot.iter body :=
      (LawfulMonad.pure_bind a (Elgot.iter body)).symm
    _ = denote (m := m) (ε := ε)
          (HasType.newest (Φ := Φ) (Γ := Γ) (β := β) (A := A)) γ (ρ, a) >>=
            Elgot.iter body := congrArg (fun x => x >>= Elgot.iter body) hn.symm
    _ = _ := by
      apply bind_congr
      intro _
      congr 1
      funext x
      unfold body
      exact congrArg
        (fun z => z >>= fun s => pure (TypeModel.coprodEquiv B A s))
        (denote_underBinder (m := m) (ε := ε) hb γ ρ a x).symm

theorem sound_iterFixpoint [LawfulElgotMonad m]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.iter ha hb) γ ρ =
      denote (m := m) (ε := ε)
        (.let₁ ha
          (.case hb HasType.newest
            (.iter HasType.newest hb.underBinder.underBinder))) γ ρ := by
  simp only [denote]
  apply bind_congr
  intro a
  let body := fun x : TyDen A =>
    denote (m := m) (ε := ε) hb γ (ρ, x) >>= fun s =>
      pure (TypeModel.coprodEquiv B A s)
  change Elgot.iter body a = _
  rw [show Elgot.iter body a =
      (body a >>= Sum.elim pure (Elgot.iter body)) from
    congrFun (LawfulElgotMonad.fixpoint body) a]
  unfold body
  rw [LawfulMonad.bind_assoc]
  apply bind_congr
  intro s
  rw [LawfulMonad.pure_bind]
  cases hs : TypeModel.coprodEquiv B A s with
  | inl x =>
      exact (denote_newest (m := m) (ε := ε) (β := .snoc β A)
        γ (ρ, a) x).symm
  | inr x =>
      have hn : denote (m := m) (ε := ε)
          (HasType.newest (Φ := Φ) (Γ := Γ) (β := .snoc β A) (A := A))
            γ ((ρ, a), x) = pure x :=
        denote_newest (m := m) (ε := ε) (β := .snoc β A) γ (ρ, a) x
      let loopBody := fun y : TyDen A =>
        denote (m := m) (ε := ε) hb γ (ρ, y) >>= fun t =>
          pure (TypeModel.coprodEquiv B A t)
      calc
        Elgot.iter loopBody x = (pure x : m _) >>= Elgot.iter loopBody :=
          (LawfulMonad.pure_bind x (Elgot.iter loopBody)).symm
        _ = denote (m := m) (ε := ε)
              (HasType.newest (Φ := Φ) (Γ := Γ) (β := .snoc β A) (A := A))
                γ ((ρ, a), x) >>= Elgot.iter loopBody :=
          congrArg (fun z => z >>= Elgot.iter loopBody) hn.symm
        _ = _ := by
          apply bind_congr
          intro _
          congr 1
          funext y
          unfold loopBody
          apply congrArg (fun z => z >>= fun t => pure (TypeModel.coprodEquiv B A t))
          calc
            denote (m := m) (ε := ε) hb γ (ρ, y) =
                denote (m := m) (ε := ε) (hb.underBinder (X := A))
                  γ ((ρ, a), y) :=
              (denote_underBinder (m := m) (ε := ε) (X := A)
                hb γ ρ a y).symm
            _ = denote (m := m) (ε := ε)
                ((hb.underBinder (X := A)).underBinder (X := A)) γ
                (((ρ, a), x), y) :=
              (denote_underBinder (m := m) (ε := ε) (X := A)
                (hb.underBinder (X := A)) γ (ρ, a) x y).symm

theorem sound_iterNaturality [LawfulElgotMonad m]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A B C : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A))
    (hc : HasType Φ Γ (.snoc β B) c C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.let₁ (.iter ha hb) hc) γ ρ =
      denote (m := m) (ε := ε)
        (.iter ha (.case hb (.inl hc.underBinder) (.inr HasType.newest))) γ ρ := by
  simp only [denote, LawfulMonad.bind_assoc]
  apply bind_congr
  intro a
  let body := fun x : TyDen A =>
    denote (m := m) (ε := ε) hb γ (ρ, x) >>= fun s =>
      pure (TypeModel.coprodEquiv B A s)
  let post := fun x : TyDen B => denote (m := m) (ε := ε) hc γ (ρ, x)
  change Elgot.kcomp (Elgot.iter body) post a = _
  rw [show Elgot.kcomp (Elgot.iter body) post =
      Elgot.iter (Elgot.mapReturn body post) from
    LawfulElgotMonad.naturality body post]
  congr 1
  funext x
  unfold Elgot.mapReturn body post
  rw [LawfulMonad.bind_assoc]
  apply bind_congr
  intro s
  rw [LawfulMonad.pure_bind]
  cases hs : TypeModel.coprodEquiv B A s with
  | inl y =>
      simp [denote_underBinder]
      simpa [Function.comp_def] using
        (bind_pure_comp (m := m) (fun z : TyDen C => Sum.inl z)
          (denote (m := m) (ε := ε) hc γ (ρ, y)))
  | inr y =>
      simp [denote_newest]

theorem sound_iterCodiagonal [LawfulElgotMonad m]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b
      (TypeFormers.coprod (TypeFormers.coprod B A) A))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε)
        (.iter ha (.iter HasType.newest hb.underBinder)) γ ρ =
      denote (m := m) (ε := ε)
        (.iter ha (.case hb HasType.newest (.inr HasType.newest))) γ ρ := by
  simp only [denote]
  apply bind_congr
  intro a
  let raw := fun x : TyDen A =>
    denote (m := m) (ε := ε) hb γ (ρ, x) >>= fun s =>
      pure (TypeModel.coprodEquiv (TypeFormers.coprod B A) A s)
  let conv := TypeModel.coprodEquiv B A
  let converted := Elgot.mapReturn raw (Elgot.liftPure conv)
  let lhs := fun x : TyDen A =>
      denote (m := m) (ε := ε)
          (HasType.newest (Φ := Φ) (Γ := Γ) (β := β) (A := A)) γ (ρ, x) >>=
        Elgot.iter (fun y =>
          denote (m := m) (ε := ε) (hb.underBinder (X := A))
              γ ((ρ, x), y) >>= fun s =>
          pure (TypeModel.coprodEquiv (TypeFormers.coprod B A) A s)) >>= fun ba =>
        pure (TypeModel.coprodEquiv B A ba)
  have hleft : lhs = Elgot.iter converted := by
    funext x
    unfold lhs
    rw [denote_newest, LawfulMonad.pure_bind]
    have hbody : (fun y : TyDen A =>
        denote (m := m) (ε := ε) (hb.underBinder (X := A))
          γ ((ρ, x), y) >>= fun s =>
        pure (TypeModel.coprodEquiv (TypeFormers.coprod B A) A s)) = raw := by
      funext y
      unfold raw
      apply congrArg
        (fun z => z >>= fun s =>
          pure (TypeModel.coprodEquiv (TypeFormers.coprod B A) A s))
      exact denote_underBinder (m := m) (ε := ε) (X := A) hb γ ρ x y
    rw [hbody]
    change Elgot.kcomp (Elgot.iter raw) (Elgot.liftPure conv) x = _
    exact congrFun (LawfulElgotMonad.naturality raw (Elgot.liftPure conv)) x
  change Elgot.iter lhs a = _
  rw [hleft]
  rw [show Elgot.iter (Elgot.iter converted) =
      Elgot.iter (Elgot.flattenBody converted) from
    LawfulElgotMonad.codiagonal converted]
  congr 1
  funext x
  unfold Elgot.flattenBody Elgot.kcomp Elgot.liftPure Elgot.flatten converted
  unfold Elgot.mapReturn raw conv
  simp only [Function.comp_apply, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
  apply bind_congr
  intro s
  cases hs : TypeModel.coprodEquiv (TypeFormers.coprod B A) A s with
  | inl ba =>
      simp
      have hn : denote (m := m) (ε := ε)
          (HasType.newest (Φ := Φ) (Γ := Γ) (β := .snoc β A)
            (A := TypeFormers.coprod B A)) γ ((ρ, x), ba) = pure ba :=
        denote_newest (m := m) (ε := ε) (β := .snoc β A) γ (ρ, x) ba
      calc
        Elgot.liftPure conv ba = pure (conv ba) := rfl
        _ = conv <$> (pure ba : m _) := (map_pure conv ba).symm
        _ = conv <$> denote (m := m) (ε := ε)
              (HasType.newest (Φ := Φ) (Γ := Γ) (β := .snoc β A)
                (A := TypeFormers.coprod B A)) γ ((ρ, x), ba) :=
          congrArg (fun z => conv <$> z) hn.symm
  | inr y =>
      simp [denote_newest]

theorem sound_iterUniformity [LawfulElgotMonad m]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {h b : Tm ν Φ (n + 1)} {b' : Tm ν Φ (n + 1)}
    {A A' B : τ}
    (ha : HasType Φ Γ β a A)
    (hh : HasType Φ Γ (.snoc β A) h A') (hp : Pure (⊥ : ε) h)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A))
    (hb' : HasType Φ Γ (.snoc β A') b' (TypeFormers.coprod B A'))
    (hsquare : ∀ (γ : CtxDen Γ) (ρA : BoundDen (.snoc β A)),
      denote (m := m) (ε := ε)
          (.case hb (.inl HasType.newest) (.inr hh.underBinder)) γ ρA =
        denote (m := m) (ε := ε) ((hb'.underBinder).instantiate hh) γ ρA)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (.iter ha hb) γ ρ =
      denote (m := m) (ε := ε) (.iter (.let₁ ha hh) hb') γ ρ := by
  classical
  let hfun := fun x : TyDen A => Classical.choose
    (denote_pure_factor (m := m) (ε := ε) hp hh γ (ρ, x))
  have hhfun (x : TyDen A) :
      denote (m := m) (ε := ε) hh γ (ρ, x) = pure (hfun x) :=
    Classical.choose_spec (denote_pure_factor (m := m) (ε := ε) hp hh γ (ρ, x))
  let f := fun x : TyDen A =>
    denote (m := m) (ε := ε) hb γ (ρ, x) >>= fun s =>
      pure (TypeModel.coprodEquiv B A s)
  let g := fun x : TyDen A' =>
    denote (m := m) (ε := ε) hb' γ (ρ, x) >>= fun s =>
      pure (TypeModel.coprodEquiv B A' s)
  have comm : Elgot.kcomp f (Elgot.liftPure (Sum.map id hfun)) =
      Elgot.kcomp (Elgot.liftPure hfun) g := by
    funext x
    have sq := hsquare γ (ρ, x)
    rw [denote_instantiate (m := m) (ε := ε)
      (hb'.underBinder (X := A)) hh γ (ρ, x) (hfun x) (hhfun x)] at sq
    rw [denote_underBinder (m := m) (ε := ε) (X := A)
      hb' γ ρ x (hfun x)] at sq
    calc
      Elgot.kcomp f (Elgot.liftPure (Sum.map id hfun)) x =
          denote (m := m) (ε := ε)
              (.case hb (.inl HasType.newest) (.inr hh.underBinder)) γ (ρ, x) >>=
            fun s => pure (TypeModel.coprodEquiv B A' s) := by
        unfold f Elgot.kcomp Elgot.liftPure
        simp only [Function.comp_apply, denote, LawfulMonad.bind_assoc,
          LawfulMonad.pure_bind]
        apply bind_congr
        intro s
        cases hs : TypeModel.coprodEquiv B A s with
        | inl y => simp [denote_newest]
        | inr y => simp [denote_underBinder, hhfun]
      _ = denote (m := m) (ε := ε) hb' γ (ρ, hfun x) >>=
            fun s => pure (TypeModel.coprodEquiv B A' s) :=
        congrArg (fun z => z >>= fun s => pure (TypeModel.coprodEquiv B A' s)) sq
      _ = Elgot.kcomp (Elgot.liftPure hfun) g x := by
        unfold g Elgot.kcomp Elgot.liftPure
        simp only [Function.comp_apply, LawfulMonad.pure_bind]
  have hu := LawfulElgotMonad.uniformity f g hfun comm
  simp only [denote, LawfulMonad.bind_assoc]
  apply bind_congr
  intro x
  change Elgot.iter f x = _
  rw [hu]
  unfold Elgot.kcomp Elgot.liftPure
  simp only [Function.comp_apply, LawfulMonad.pure_bind]
  rw [hhfun x, LawfulMonad.pure_bind]
  change Elgot.iter g (hfun x) = Elgot.iter g (hfun x)
  rfl

/-- Every proof-relevant typed equation preserves denotation. -/
theorem sound [LawfulElgotMonad m]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (d : TypedEquiv.Deriv (⊥ : ε) Γ ha hb) :
    ∀ (γ : CtxDen Γ) (ρ : BoundDen β),
      denote (m := m) (ε := ε) ha γ ρ = denote (m := m) (ε := ε) hb γ ρ := by
  induction d with
  | refl => intro γ ρ; rfl
  | symm _ ih => intro γ ρ; exact (ih γ ρ).symm
  | trans _ _ ih₁ ih₂ => intro γ ρ; exact (ih₁ γ ρ).trans (ih₂ γ ρ)
  | sub _ _ ih =>
      intro γ ρ
      simp only [denote]
      rw [ih γ ρ]
  | op _ ih =>
      intro γ ρ
      simp only [denote]
      rw [ih γ ρ]
  | let₁ _ _ ih₁ ih₂ =>
      intro γ ρ
      simp only [denote]
      rw [ih₁ γ ρ]
      apply bind_congr
      intro x
      exact ih₂ γ (ρ, x)
  | pair _ _ ih₁ ih₂ =>
      intro γ ρ
      simp only [denote]
      rw [ih₁ γ ρ]
      apply bind_congr
      intro x
      rw [ih₂ γ ρ]
  | let₂ _ _ ih₁ ih₂ =>
      intro γ ρ
      simp only [denote]
      rw [ih₁ γ ρ]
      apply bind_congr
      intro x
      exact ih₂ γ _
  | inl _ ih =>
      intro γ ρ
      simp only [denote]
      rw [ih γ ρ]
  | inr _ ih =>
      intro γ ρ
      simp only [denote]
      rw [ih γ ρ]
  | case _ _ _ ihe ihl ihr =>
      intro γ ρ
      simp only [denote]
      rw [ihe γ ρ]
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl x => exact ihl γ (ρ, x)
      | inr x => exact ihr γ (ρ, x)
  | abort _ ih =>
      intro γ ρ
      simp only [denote]
      rw [ih γ ρ]
  | iter _ _ ih₁ ih₂ =>
      intro γ ρ
      simp only [denote]
      rw [ih₁ γ ρ]
      apply bind_congr
      intro x
      congr 1
      funext y
      rw [ih₂ γ (ρ, y)]
  | letBeta hp ha hb => exact sound_letBeta hp ha hb
  | letEta ha => exact sound_letEta ha
  | unitEta ha => exact sound_unitEta ha
  | pairBeta ha hb hc => exact sound_pairBeta ha hb hc
  | pairEta ha => exact sound_pairEta ha
  | caseBetaL he hl hr => exact sound_caseBetaL he hl hr
  | caseBetaR he hl hr => exact sound_caseBetaR he hl hr
  | caseEta he => exact sound_caseEta he
  | bindOp ha hc => exact sound_bindOp ha hc
  | bindLet ha hb hc => exact sound_bindLet ha hb hc
  | bindLetPair he hc hd => exact sound_bindLetPair he hc hd
  | bindLetCase he hl hr hd => exact sound_bindLetCase he hl hr hd
  | bindPair ha hc => exact sound_bindPair ha hc
  | bindCase he hl hr => exact sound_bindCase he hl hr
  | emptyInitial ha hb hc => exact sound_emptyInitial ha hb hc
  | iterFixpoint ha hb => exact sound_iterFixpoint ha hb
  | iterNaturality ha hb hc => exact sound_iterNaturality ha hb hc
  | iterCodiagonal ha hb => exact sound_iterCodiagonal ha hb
  | iterUniformity ha hh hp hb hb' _ ih =>
      exact sound_iterUniformity ha hh hp hb hb' ih
  | iterBind ha hb => exact sound_iterBind ha hb

/-- Proposition-truncated typed equality is sound at its fixed endpoints. -/
theorem related_sound [LawfulElgotMonad m]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (h : TypedEquiv.Related (⊥ : ε) Γ ha hb)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) ha γ ρ = denote (m := m) (ε := ε) hb γ ρ :=
  h.elim fun d => sound d γ ρ

end Isotope.LambdaIter.Subtyping.Semantics
