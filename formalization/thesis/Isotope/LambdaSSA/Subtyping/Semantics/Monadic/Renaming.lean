import Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Region
import Isotope.LambdaSSA.Subtyping.Structural
import Isotope.LambdaSSA.Semantics.Monadic.Renaming

/-! # Renaming for proof-relevant monadic SSA semantics -/

namespace Isotope.LambdaSSA.Subtyping.Semantics.Monadic

set_option relaxedAutoImplicit true

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaSSA.Semantics.Monadic

universe u v q r

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
  [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]

theorem Denotes.renameVars {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) {a : LambdaSSA.Tm Φ} {A : τ}
    {ha : LambdaSSA.Subtyping.Tm.HasType Γ a A}
    {f : Env Γ → m (TyDen A)} (d : Denotes ε ha f) :
    Denotes ε (ha.rename hρ) (fun δ => f (Env.rename hρ δ)) := by
  induction d generalizing Δ ρ with
  | var h => simpa using Denotes.var (m := m) (ε := ε) (hρ h)
  | op d ih => exact .op (ih hρ)
  | let₁ da db iha ihb =>
      convert Denotes.let₁ (iha hρ) (ihb (hρ.lift _)) using 1
      funext δ
      apply bind_congr
      intro a
      rw [Env.rename_lift]
  | pair da db iha ihb => exact .pair (iha hρ) (ihb hρ)
  | unit => exact .unit
  | let₂ da db iha ihb =>
      convert Denotes.let₂ (iha hρ) (ihb ((hρ.lift _).lift _)) using 1
      funext δ
      apply bind_congr
      intro ab
      dsimp only
      let p := TypeModel.tensorEquiv _ _ ab
      apply congrArg
      exact ((Env.rename_lift (hρ.lift _) (δ, p.1) _ p.2).trans
        (congrArg (fun z => (z, p.2)) (Env.rename_lift hρ δ _ p.1))).symm
  | inl d ih => exact .inl (ih hρ)
  | inr d ih => exact .inr (ih hρ)
  | case de dl dr ihe ihl ihr =>
      convert Denotes.case (ihe hρ) (ihl (hρ.lift _)) (ihr (hρ.lift _)) using 1
      funext δ
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl x =>
          simp only
          apply congrArg
          exact (Env.rename_lift hρ δ _ x).symm
      | inr x =>
          simp only
          apply congrArg
          exact (Env.rename_lift hρ δ _ x).symm
  | abort d ih => exact .abort (ih hρ)
  | sub d witness ih => exact .sub (ih hρ) witness

theorem RegionDenotes.renameVars {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) {region : LambdaSSA.Region Φ}
    {L : LambdaSSA.LCtx τ}
    {hr : LambdaSSA.Subtyping.Region.HasType Γ region L}
    {f : Env Γ → m (LabelDen L)} (d : RegionDenotes ε hr f) :
    RegionDenotes ε (hr.renameVars hρ) (fun δ => f (Env.rename hρ δ)) := by
  induction d generalizing Δ ρ with
  | br dt => exact .br (dt.renameVars hρ)
  | case de dl dr ihl ihr =>
      convert RegionDenotes.case (de.renameVars hρ)
        (ihl (hρ.lift _)) (ihr (hρ.lift _)) using 1
      funext δ
      apply bind_congr
      intro e
      cases TypeModel.coprodEquiv _ _ e with
      | inl x =>
          simp only
          apply congrArg
          exact (Env.rename_lift hρ δ _ x).symm
      | inr x =>
          simp only
          apply congrArg
          exact (Env.rename_lift hρ δ _ x).symm
  | let₁ da db ihb =>
      convert RegionDenotes.let₁ (da.renameVars hρ) (ihb (hρ.lift _)) using 1
      funext δ
      apply bind_congr
      intro a
      rw [Env.rename_lift]
  | let₂ da db ihb =>
      convert RegionDenotes.let₂ (da.renameVars hρ)
        (ihb ((hρ.lift _).lift _)) using 1
      funext δ
      apply bind_congr
      intro ab
      dsimp only
      let p := TypeModel.tensorEquiv _ _ ab
      apply congrArg
      exact ((Env.rename_lift (hρ.lift _) (δ, p.1) _ p.2).trans
        (congrArg (fun z => (z, p.2)) (Env.rename_lift hρ δ _ p.1))).symm
  | cfgZero he hb de ih =>
      exact RegionDenotes.cfgZero (he.renameVars hρ)
        (fun i => (hb i).renameVars (hρ.lift _)) (ih hρ)
  | @cfg n R Γ L entry blocks he hb fe fb collective de db dc ihe ihb =>
      let fb' : ∀ i, Env (R i :: Δ) → m (LabelDen (List.ofFn R ++ L)) :=
        fun i δ => fb i (Env.rename (hρ.lift _) δ)
      let collective' : Env Δ × FiniteLabelDen R →
          m (LabelDen (List.ofFn R ++ L)) :=
        fun p => collective (Env.rename hρ p.1, p.2)
      have dc' : CollectiveDenotes Δ R L fb' collective' := by
        constructor
        intro i δ a
        simp only [collective', fb']
        rw [Env.rename_lift]
        exact dc.restrict i (Env.rename hρ δ) a
      exact RegionDenotes.cfg _ _ (ihe hρ)
        (fun i => ihb i (hρ.lift _)) dc'

end Isotope.LambdaSSA.Subtyping.Semantics.Monadic
