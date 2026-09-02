import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborateCase

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

private def iterContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {X C : τ}
    (hb : HasType Φ Γ (.snoc β X) b (LambdaIter.coprod C X)) :
    Program.HasType Γ (.snoc β X)
      (.let₁
        (.iter (.bv 0)
          (programRename (TypedRenaming.underBinder β X X).toFun (elaborate b)))
        (.ret (.bv 0))) C :=
  .let₁
    (.iter
      (show Atom.HasType Γ (.snoc β X) (.bv 0) X from .bv)
      (programRename_hasType (TypedRenaming.underBinder β X X) (elaborate_hasType hb)))
    (.ret (show Atom.HasType Γ (.snoc (.snoc β X) C) (.bv 0) C from .bv))

private theorem denote_toGeneric_iter {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {aard : Tm ν Φ (n + 1)} {X C : τ}
    (ha : HasType Φ Γ β a X)
    (hb : HasType Φ Γ (.snoc β X) aard (LambdaIter.coprod C X))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.iter ha hb).toGeneric γ ρ =
      (denote (m := m) (ε := ε) ha.toGeneric γ ρ >>= Elgot.iter fun x =>
        denote (m := m) (ε := ε) hb.toGeneric γ (ρ, x) >>= fun s =>
          pure (TypeModel.coprodEquiv C X s)) := by
  simp only [Isotope.LambdaIter.LocallyNameless.HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.denote]

theorem denote_elaborate_iter {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {X C : τ}
    (ha : HasType Φ Γ β a X)
    (hb : HasType Φ Γ (.snoc β X) b (LambdaIter.coprod C X))
    (γ : CtxDen Γ)
    (iha : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType ha) γ ρ =
      denote (m := m) (ε := ε) ha.toGeneric γ ρ)
    (ihb : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType hb) γ ρ =
      denote (m := m) (ε := ε) hb.toGeneric γ ρ)
    (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (elaborate_hasType (HasType.iter ha hb)) γ ρ =
      denote (m := m) (ε := ε) (HasType.iter ha hb).toGeneric γ ρ := by
  let hk := iterContinuation hb
  calc
    _ = denoteProgram (elaborate_hasType ha) γ ρ >>= fun x =>
          denoteProgram hk γ (ρ, x) :=
      denote_bind (hp := elaborate_hasType ha) (hk := hk) γ ρ
    _ = (denote (m := m) (ε := ε) ha.toGeneric γ ρ >>= Elgot.iter fun x =>
          denote (m := m) (ε := ε) hb.toGeneric γ (ρ, x) >>= fun s =>
            pure (TypeModel.coprodEquiv C X s)) := by
      show (denoteProgram (ε := ε) (m := m) (elaborate_hasType ha) γ ρ >>= fun x =>
          denoteProgram (ε := ε) (m := m) hk γ (ρ, x)) = _
      rw [iha ρ]
      apply bind_congr
      intro x
      let hx : Atom.HasType (Φ := Φ) Γ (.snoc β X) (.bv 0) X := .bv
      let F : TypeModel.interp X → m (TypeModel.interp C ⊕ TypeModel.interp X) := fun x' =>
        denoteProgram (ε := ε) (m := m)
          (programRename_hasType (TypedRenaming.underBinder β X X) (elaborate_hasType hb))
          γ ((ρ, x), x') >>= fun s => pure (TypeModel.coprodEquiv C X s)
      dsimp [hk, iterContinuation, denoteProgram, denoteInstr, denoteAtom]
      unfold BoundDen.get
      simp only [Fin.cases_zero]
      change ((pure x >>= Elgot.iter F) >>= pure) =
        Elgot.iter (fun x' => denote (m := m) (ε := ε) hb.toGeneric γ (ρ, x') >>= fun s =>
          pure (TypeModel.coprodEquiv C X s)) x
      rw [bind_pure, LawfulMonad.pure_bind]
      apply congrFun
      apply congrArg Elgot.iter
      funext x'
      dsimp [F]
      rw [denote_programRename (elaborate_hasType hb)
        (TypedRenaming.underBinder β X X) γ ((ρ, x), x')]
      have ep : BoundDen.pull
          ({ toFun := (TypedRenaming.underBinder β X X).toFun,
             typed := (TypedRenaming.underBinder β X X).typed } :
            Isotope.LambdaIter.Subtyping.LocallyNameless.TypedRenaming
              (.snoc β X) (.snoc (.snoc β X) X))
          ((ρ, x), x') = (ρ, x') := BoundDen.pull_underBinder β X X ρ x x'
      rw [ep, ihb (ρ, x')]
    _ = _ := (denote_toGeneric_iter ha hb γ ρ).symm

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
