import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborateLetTwo

namespace Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct

open Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.Semantics

universe u v w q r
variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

private def caseContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {l r : Tm ν Φ (n + 1)} {X Y C : τ}
    (hl : HasType Φ Γ (.snoc β X) l C) (hr : HasType Φ Γ (.snoc β Y) r C) :
    Program.HasType Γ (.snoc β (LambdaIter.coprod X Y))
      (.let₁
        (.case (.bv 0)
          (programRename (TypedRenaming.underBinder β (LambdaIter.coprod X Y) X).toFun
            (elaborate l))
          (programRename (TypedRenaming.underBinder β (LambdaIter.coprod X Y) Y).toFun
            (elaborate r)))
        (.ret (.bv 0))) C :=
  .let₁
    (.case
      (show Atom.HasType Γ (.snoc β (LambdaIter.coprod X Y)) (.bv 0)
        (LambdaIter.coprod X Y) from .bv)
      (programRename_hasType (TypedRenaming.underBinder β (LambdaIter.coprod X Y) X)
        (elaborate_hasType hl))
      (programRename_hasType (TypedRenaming.underBinder β (LambdaIter.coprod X Y) Y)
        (elaborate_hasType hr)))
    (.ret (show Atom.HasType Γ
      (.snoc (.snoc β (LambdaIter.coprod X Y)) C) (.bv 0) C from .bv))

private theorem denote_toGeneric_case {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {X Y C : τ}
    (he : HasType Φ Γ β e (LambdaIter.coprod X Y))
    (hl : HasType Φ Γ (.snoc β X) l C) (hr : HasType Φ Γ (.snoc β Y) r C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.case he hl hr).toGeneric γ ρ =
      (denote (m := m) (ε := ε) he.toGeneric γ ρ >>= fun e =>
        match TypeModel.coprodEquiv X Y e with
        | .inl x => denote (m := m) (ε := ε) hl.toGeneric γ (ρ, x)
        | .inr y => denote (m := m) (ε := ε) hr.toGeneric γ (ρ, y)) := by
  simp only [Isotope.LambdaIter.LocallyNameless.HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.denote]
  rfl

theorem denote_elaborate_case {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {X Y C : τ}
    (he : HasType Φ Γ β e (LambdaIter.coprod X Y))
    (hl : HasType Φ Γ (.snoc β X) l C) (hr : HasType Φ Γ (.snoc β Y) r C)
    (γ : CtxDen Γ)
    (ihe : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType he) γ ρ =
      denote (m := m) (ε := ε) he.toGeneric γ ρ)
    (ihl : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType hl) γ ρ =
      denote (m := m) (ε := ε) hl.toGeneric γ ρ)
    (ihr : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType hr) γ ρ =
      denote (m := m) (ε := ε) hr.toGeneric γ ρ)
    (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (elaborate_hasType (HasType.case he hl hr)) γ ρ =
      denote (m := m) (ε := ε) (HasType.case he hl hr).toGeneric γ ρ := by
  let hk := caseContinuation hl hr
  calc
    _ = denoteProgram (elaborate_hasType he) γ ρ >>= fun e =>
          denoteProgram hk γ (ρ, e) :=
      denote_bind (hp := elaborate_hasType he) (hk := hk) γ ρ
    _ = (denote (m := m) (ε := ε) he.toGeneric γ ρ >>= fun e =>
          match TypeModel.coprodEquiv X Y e with
          | .inl x => denote (m := m) (ε := ε) hl.toGeneric γ (ρ, x)
          | .inr y => denote (m := m) (ε := ε) hr.toGeneric γ (ρ, y)) := by
      show (denoteProgram (ε := ε) (m := m) (elaborate_hasType he) γ ρ >>= fun e =>
          denoteProgram (ε := ε) (m := m) hk γ (ρ, e)) =
        (denote (m := m) (ε := ε) he.toGeneric γ ρ >>= fun e =>
          match TypeModel.coprodEquiv X Y e with
          | .inl x => denote (m := m) (ε := ε) hl.toGeneric γ (ρ, x)
          | .inr y => denote (m := m) (ε := ε) hr.toGeneric γ (ρ, y))
      rw [ihe ρ]
      apply bind_congr
      intro e
      let he' : Atom.HasType (Φ := Φ) Γ (.snoc β (LambdaIter.coprod X Y)) (.bv 0)
          (LambdaIter.coprod X Y) := .bv
      have ee : denoteAtom (ε := ε) (m := m) he' γ (ρ, e) = pure e := by rfl
      let F : TypeModel.interp (LambdaIter.coprod X Y) → m (TypeModel.interp C) := fun e' =>
        match TypeModel.coprodEquiv X Y e' with
        | .inl x => denoteProgram (ε := ε) (m := m)
            (programRename_hasType (TypedRenaming.underBinder β (LambdaIter.coprod X Y) X)
              (elaborate_hasType hl)) γ ((ρ, e), x)
        | .inr y => denoteProgram (ε := ε) (m := m)
            (programRename_hasType (TypedRenaming.underBinder β (LambdaIter.coprod X Y) Y)
              (elaborate_hasType hr)) γ ((ρ, e), y)
      dsimp [hk, caseContinuation, denoteProgram, denoteInstr, denoteAtom]
      unfold BoundDen.get
      simp only [Fin.cases_zero]
      change ((pure e >>= F) >>= pure) =
        (match TypeModel.coprodEquiv X Y e with
        | .inl x => denote (m := m) (ε := ε) hl.toGeneric γ (ρ, x)
        | .inr y => denote (m := m) (ε := ε) hr.toGeneric γ (ρ, y))
      rw [bind_pure, LawfulMonad.pure_bind]
      dsimp [F]
      cases hs : TypeModel.coprodEquiv X Y e with
      | inl x =>
          simp only
          rw [denote_programRename (elaborate_hasType hl)
            (TypedRenaming.underBinder β (LambdaIter.coprod X Y) X) γ ((ρ, e), x)]
          have ep : BoundDen.pull
              ({ toFun := (TypedRenaming.underBinder β (LambdaIter.coprod X Y) X).toFun,
                 typed := (TypedRenaming.underBinder β (LambdaIter.coprod X Y) X).typed } :
                Isotope.LambdaIter.Subtyping.LocallyNameless.TypedRenaming
                  (.snoc β X) (.snoc (.snoc β (LambdaIter.coprod X Y)) X))
              ((ρ, e), x) = (ρ, x) :=
            BoundDen.pull_underBinder β (LambdaIter.coprod X Y) X ρ e x
          rw [ep, ihl (ρ, x)]
      | inr y =>
          simp only
          rw [denote_programRename (elaborate_hasType hr)
            (TypedRenaming.underBinder β (LambdaIter.coprod X Y) Y) γ ((ρ, e), y)]
          have ep : BoundDen.pull
              ({ toFun := (TypedRenaming.underBinder β (LambdaIter.coprod X Y) Y).toFun,
                 typed := (TypedRenaming.underBinder β (LambdaIter.coprod X Y) Y).typed } :
                Isotope.LambdaIter.Subtyping.LocallyNameless.TypedRenaming
                  (.snoc β Y) (.snoc (.snoc β (LambdaIter.coprod X Y)) Y))
              ((ρ, e), y) = (ρ, y) :=
            BoundDen.pull_underBinder β (LambdaIter.coprod X Y) Y ρ e y
          rw [ep, ihr (ρ, y)]
    _ = _ := (denote_toGeneric_case he hl hr γ ρ).symm

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
