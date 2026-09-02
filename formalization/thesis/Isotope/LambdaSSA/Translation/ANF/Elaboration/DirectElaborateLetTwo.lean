import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaboratePair

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

private def letTwoContinuation {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 2)} {X Y C : τ}
    (hb : HasType Φ Γ (.snoc (.snoc β X) Y) b C) :
    Program.HasType Γ (.snoc β (LambdaIter.tensor X Y))
      (.let₂ (.bv 0)
        (programRename
          (TypedRenaming.underTwoBinders β (LambdaIter.tensor X Y) X Y).toFun
          (elaborate b))) C :=
  .let₂
    (show Atom.HasType Γ (.snoc β (LambdaIter.tensor X Y)) (.bv 0)
      (LambdaIter.tensor X Y) from .bv)
    (programRename_hasType
      (TypedRenaming.underTwoBinders β (LambdaIter.tensor X Y) X Y)
      (elaborate_hasType hb))

private theorem denote_toGeneric_let₂ {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)} {X Y C : τ}
    (ha : HasType Φ Γ β a (LambdaIter.tensor X Y))
    (hb : HasType Φ Γ (.snoc (.snoc β X) Y) b C)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) (HasType.let₂ ha hb).toGeneric γ ρ =
      (denote (m := m) (ε := ε) ha.toGeneric γ ρ >>= fun xy =>
        let p := TypeModel.tensorEquiv X Y xy
        denote (m := m) (ε := ε) hb.toGeneric γ ((ρ, p.1), p.2)) := by
  simp only [Isotope.LambdaIter.LocallyNameless.HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.denote]

theorem denote_elaborate_let₂ {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)} {X Y C : τ}
    (ha : HasType Φ Γ β a (LambdaIter.tensor X Y))
    (hb : HasType Φ Γ (.snoc (.snoc β X) Y) b C)
    (γ : CtxDen Γ)
    (iha : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType ha) γ ρ =
      denote (m := m) (ε := ε) ha.toGeneric γ ρ)
    (ihb : ∀ ρ, denoteProgram (ε := ε) (m := m) (elaborate_hasType hb) γ ρ =
      denote (m := m) (ε := ε) hb.toGeneric γ ρ)
    (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (elaborate_hasType (HasType.let₂ ha hb)) γ ρ =
      denote (m := m) (ε := ε) (HasType.let₂ ha hb).toGeneric γ ρ := by
  let hk := letTwoContinuation hb
  calc
    _ = denoteProgram (elaborate_hasType ha) γ ρ >>= fun xy =>
          denoteProgram hk γ (ρ, xy) :=
      denote_bind (hp := elaborate_hasType ha) (hk := hk) γ ρ
    _ = (denote ha.toGeneric γ ρ >>= fun xy =>
          let p := TypeModel.tensorEquiv X Y xy
          denote hb.toGeneric γ ((ρ, p.1), p.2)) := by
      rw [iha ρ]
      apply bind_congr
      intro xy
      let p := TypeModel.tensorEquiv X Y xy
      let hxy : Atom.HasType (Φ := Φ) Γ (.snoc β (LambdaIter.tensor X Y)) (.bv 0)
          (LambdaIter.tensor X Y) := .bv
      have exy : denoteAtom (ε := ε) (m := m) hxy γ (ρ, xy) = pure xy := by rfl
      dsimp [hk, letTwoContinuation, denoteProgram, denoteAtom]
      change (denoteAtom (ε := ε) (m := m) hxy γ (ρ, xy) >>= fun ab =>
        denoteProgram
          (programRename_hasType
            (TypedRenaming.underTwoBinders β (LambdaIter.tensor X Y) X Y)
            (elaborate_hasType hb)) γ
          (((ρ, xy), (TypeModel.tensorEquiv X Y ab).1),
            (TypeModel.tensorEquiv X Y ab).2)) = _
      rw [exy]
      simp only [pure_bind]
      rw [denote_programRename (elaborate_hasType hb)
        (TypedRenaming.underTwoBinders β (LambdaIter.tensor X Y) X Y) γ
        (((ρ, xy), p.1), p.2)]
      have ep : BoundDen.pull
          ({ toFun := (TypedRenaming.underTwoBinders β (LambdaIter.tensor X Y) X Y).toFun,
             typed := (TypedRenaming.underTwoBinders β (LambdaIter.tensor X Y) X Y).typed } :
            Isotope.LambdaIter.Subtyping.LocallyNameless.TypedRenaming
              (.snoc (.snoc β X) Y)
              (.snoc (.snoc (.snoc β (LambdaIter.tensor X Y)) X) Y))
          (((ρ, xy), p.1), p.2) = ((ρ, p.1), p.2) :=
        BoundDen.pull_underTwoBinders β (LambdaIter.tensor X Y) X Y ρ xy p.1 p.2
      rw [ep]
      exact ihb ((ρ, p.1), p.2)
    _ = _ := (denote_toGeneric_let₂ ha hb γ ρ).symm

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
