import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborateAbort

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

private def pairReturn {Γ : Ctx ν τ} {β : BoundCtx τ n} (Φ : Type q)
    [HasTy Φ τ] (X Y : τ) :
    Program.HasType (Φ := Φ) Γ (.snoc (.snoc β X) Y)
      (.ret (.pair (.bv 1 : Atom ν Φ (n + 2)) (.bv 0))) (LambdaIter.tensor X Y) :=
  .ret (.pair
    (show Atom.HasType (Φ := Φ) Γ (.snoc (.snoc β X) Y) (.bv 1) X from .bv)
    (show Atom.HasType (Φ := Φ) Γ (.snoc (.snoc β X) Y) (.bv 0) Y from .bv))

private theorem denote_pairReturn {Γ : Ctx ν τ} {β : BoundCtx τ n} (X Y : τ)
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : TypeModel.interp X) (y : TypeModel.interp Y) :
    denoteProgram (ε := ε) (m := m)
      (pairReturn (ν := ν) (Γ := Γ) (β := β) Φ X Y) γ ((ρ, x), y) =
      (pure ((TypeModel.tensorEquiv X Y).symm (x, y)) :
        m (TypeModel.interp (LambdaIter.tensor X Y))) := by
  let hx : Atom.HasType (Φ := Φ) Γ (.snoc (.snoc β X) Y) (.bv 1) X := .bv
  let hy : Atom.HasType (Φ := Φ) Γ (.snoc (.snoc β X) Y) (.bv 0) Y := .bv
  have ehx : denoteAtom (ε := ε) (m := m) hx γ ((ρ, x), y) = pure x := by rfl
  have ehy : denoteAtom (ε := ε) (m := m) hy γ ((ρ, x), y) = pure y := by rfl
  unfold pairReturn denoteProgram denoteAtom
  change (denoteAtom (ε := ε) (m := m) hx γ ((ρ, x), y) >>= fun x =>
    denoteAtom (ε := ε) (m := m) hy γ ((ρ, x), y) >>= fun y =>
    pure ((TypeModel.tensorEquiv X Y).symm (x, y))) = _
  rw [ehx]
  simp only [pure_bind]
  rw [ehy]
  simp
  rfl

private def pairContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {b : Tm ν Φ n} (hb : HasType Φ Γ β b Y) (X : τ) :
    Program.HasType Γ (.snoc β X)
      (bind (programRename Fin.succ (elaborate b))
        (.ret (.pair (.bv 1) (.bv 0)))) (LambdaIter.tensor X Y) :=
  bind_hasType
    (programRename_hasType (TypedRenaming.succ β X) (elaborate_hasType hb))
    (pairReturn (ν := ν) (Γ := Γ) (β := β) Φ X Y)

private theorem denote_toGeneric_pair {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {X Y : τ} (ha : HasType Φ Γ β a X) (hb : HasType Φ Γ β b Y)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.pair ha hb).toGeneric γ ρ =
      (denote (m := m) (ε := ε) ha.toGeneric γ ρ >>= fun x =>
       denote (m := m) (ε := ε) hb.toGeneric γ ρ >>= fun y =>
       pure ((TypeModel.tensorEquiv X Y).symm (x, y))) := by
  simp only [Isotope.LambdaIter.LocallyNameless.HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.denote]
  rfl

theorem denote_elaborate_pair {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {X Y : τ} (ha : HasType Φ Γ β a X) (hb : HasType Φ Γ β b Y)
    (γ : CtxDen Γ)
    (iha : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType ha) γ ρ =
      denote (m := m) (ε := ε) ha.toGeneric γ ρ)
    (ihb : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType hb) γ ρ =
      denote (m := m) (ε := ε) hb.toGeneric γ ρ)
    (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (elaborate_hasType (HasType.pair ha hb)) γ ρ =
      denote (m := m) (ε := ε) (HasType.pair ha hb).toGeneric γ ρ := by
  let hk := pairContinuation hb X
  let hr := pairReturn (ν := ν) (Γ := Γ) (β := β) Φ X Y
  let hp := programRename_hasType (TypedRenaming.succ β X) (elaborate_hasType hb)
  calc
    _ = denoteProgram (elaborate_hasType ha) γ ρ >>= fun x =>
          denoteProgram hk γ (ρ, x) :=
      denote_bind (hp := elaborate_hasType ha) (hk := hk) γ ρ
    _ = denoteProgram (elaborate_hasType ha) γ ρ >>= fun x =>
          (denoteProgram hp γ (ρ, x) >>= fun y => denoteProgram hr γ ((ρ, x), y)) := by
      apply bind_congr
      intro x
      exact denote_bind (hp := hp) (hk := hr) γ (ρ, x)
    _ = (denote ha.toGeneric γ ρ >>= fun x =>
          (denote hb.toGeneric γ ρ >>= fun y =>
            (pure ((TypeModel.tensorEquiv X Y).symm (x, y)) :
              m (TypeModel.interp (LambdaIter.tensor X Y))))) := by
      rw [iha ρ]
      apply bind_congr
      intro x
      rw [denote_programRename (elaborate_hasType hb) (TypedRenaming.succ β X) γ (ρ, x)]
      have ep : BoundDen.pull
          ({ toFun := (TypedRenaming.succ β X).toFun,
             typed := (TypedRenaming.succ β X).typed } :
            Isotope.LambdaIter.Subtyping.LocallyNameless.TypedRenaming β (.snoc β X))
          (ρ, x) = ρ := BoundDen.pull_succ β X ρ x
      rw [ep]
      rw [ihb ρ]
      apply bind_congr
      exact denote_pairReturn X Y γ ρ x
    _ = _ := (denote_toGeneric_pair ha hb γ ρ).symm

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
