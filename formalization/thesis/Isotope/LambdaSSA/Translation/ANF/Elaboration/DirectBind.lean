import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectRenaming

/-! # Direct semantics of administrative binding -/

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

private def insertTwo (β : BoundCtx τ n) (X Y : τ) :
    TypedRenaming β (.snoc (.snoc β X) Y) where
  toFun i := Fin.succ (Fin.succ i)
  typed := fun _ => rfl

private def asGeneric {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (s : TypedRenaming β β') :
    Isotope.LambdaIter.Subtyping.LocallyNameless.TypedRenaming β β' :=
  { toFun := s.toFun, typed := s.typed }

private theorem pull_insertTwo (β : BoundCtx τ n) (X Y : τ)
    (ρ : BoundDen β) (x : TypeModel.interp X) (y : TypeModel.interp Y) :
    BoundDen.pull (asGeneric (insertTwo β X Y)) ((ρ, x), y) = ρ := by
  induction β with
  | nil => rfl
  | snoc β A ih =>
      apply Prod.ext
      · exact ih ρ.1
      · rfl

private def insertTwoUnder (β : BoundCtx τ n) (X Y A : τ) :
    TypedRenaming (.snoc β A) (.snoc (.snoc (.snoc β X) Y) A) :=
  (insertTwo β X Y).up A

@[simp] private theorem pull_insertTwoUnder (β : BoundCtx τ n) (X Y A : τ)
    (ρ : BoundDen β) (x : TypeModel.interp X) (y : TypeModel.interp Y)
    (a : TypeModel.interp A) :
    BoundDen.pull (asGeneric (insertTwoUnder β X Y A)) (((ρ, x), y), a) = (ρ, a) := by
  change BoundDen.pull ((asGeneric (insertTwo β X Y)).up A) (((ρ, x), y), a) = _
  rw [BoundDen.pull_up, pull_insertTwo]

private theorem pull_underBinder_exact (β : BoundCtx τ n) (X Y : τ)
    (ρ : BoundDen β) (x : TypeModel.interp X) (y : TypeModel.interp Y) :
    BoundDen.pull (asGeneric (TypedRenaming.underBinder β X Y)) ((ρ, x), y) = (ρ, y) := by
  exact BoundDen.pull_underBinder β X Y ρ x y

/-- Direct evaluation of administrative `bind` is monadic sequencing. -/
theorem denote_bind {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {p : Program ν Φ n} {A B : τ} {k : Program ν Φ (n + 1)}
    (hp : Program.HasType Γ β p A)
    (hk : Program.HasType Γ (.snoc β A) k B)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteProgram (ε := ε) (m := m) (bind_hasType hp hk) γ ρ =
      (denoteProgram (ε := ε) (m := m) hp γ ρ >>= fun a =>
        denoteProgram (ε := ε) (m := m) hk γ (ρ, a)) := by
  induction hp using Program.HasType.rec
      (motive_2 := fun _ _ _ _ => True) generalizing B with
  | ret ha => rfl
  | @let₁ X Y n₀ β₀ i hi body hb _ ih =>
      simp only [bind_hasType, bind, denoteProgram, LawfulMonad.bind_assoc]
      apply bind_congr
      intro x
      rw [ih]
      apply bind_congr
      intro a
      change denoteProgram (programRename_hasType
        (TypedRenaming.underBinder β₀ X Y) hk) γ ((ρ, x), a) = _
      calc
        _ = denoteProgram hk γ (BoundDen.pull
            (asGeneric (TypedRenaming.underBinder β₀ X Y)) ((ρ, x), a)) :=
          denote_programRename (ε := ε) (m := m) hk
            (TypedRenaming.underBinder β₀ X Y) γ ((ρ, x), a)
        _ = _ := congrArg (denoteProgram (ε := ε) (m := m) hk γ)
          (pull_underBinder_exact β₀ X Y ρ x a)
  | @let₂ X Y Z n₀ β₀ atom ha body hb ih =>
      simp only [bind_hasType, bind, denoteProgram, LawfulMonad.bind_assoc]
      apply bind_congr
      intro ab
      rw [ih]
      apply bind_congr
      intro a
      change denoteProgram (programRename_hasType
        (insertTwoUnder β₀ X Y Z) hk) γ
          (((ρ, (TypeModel.tensorEquiv _ _ ab).1),
            (TypeModel.tensorEquiv _ _ ab).2), a) = _
      calc
        _ = denoteProgram hk γ (BoundDen.pull
            (asGeneric (insertTwoUnder β₀ X Y Z))
            (((ρ, (TypeModel.tensorEquiv X Y ab).1),
              (TypeModel.tensorEquiv X Y ab).2), a)) :=
          denote_programRename (ε := ε) (m := m) hk
            (insertTwoUnder β₀ X Y Z) γ
            (((ρ, (TypeModel.tensorEquiv X Y ab).1),
              (TypeModel.tensorEquiv X Y ab).2), a)
        _ = _ := congrArg (denoteProgram (ε := ε) (m := m) hk γ)
          (pull_insertTwoUnder β₀ X Y Z ρ
            (TypeModel.tensorEquiv X Y ab).1 (TypeModel.tensorEquiv X Y ab).2 a)
  | atom | case | iter => trivial

end Isotope.LambdaSSA.Translation.ANF.Elaboration.Direct
