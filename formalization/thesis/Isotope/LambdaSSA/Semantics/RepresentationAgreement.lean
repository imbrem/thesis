import Isotope.LambdaSSA.LocallyNameless.ToDeBruijn.Typing
import Isotope.LambdaSSA.Named.ToLocallyNameless.Typing
import Isotope.LambdaSSA.Semantics.Term
import Isotope.LambdaSSA.Semantics.Region
import Isotope.LambdaSSA.Semantics.Monadic.Term

/-! # Semantic wrappers for closed surface representations -/

namespace Isotope.LambdaSSA.Semantics.RepresentationAgreement

open CategoryTheory CategoryTheory.Limits

def emptyLabelAlignment : Named.ToLocallyNameless.LookupAligned
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
    (LambdaIter.Named.ToLocallyNameless.Scope.nil)
    (LambdaIter.LocallyNameless.BoundCtx.nil)
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) :=
  Named.ToLocallyNameless.LookupAligned.of_aligned (.nil)

namespace Categorical

open Isotope.LambdaIter.Subtyping.Semantics.Categorical

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : TypeModel τ V)
  {Φ : Type u₄} [LambdaIter.HasTy Φ τ] [InstructionModel J M Φ]

noncomputable def denoteLocallyNamelessTm
    {β : LocallyNameless.BoundCtx τ n} {t : LocallyNameless.Tm Empty Φ n}
    (h : LocallyNameless.Tm.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    J.obj (Semantics.Categorical.ctxObj M
      (LocallyNameless.ToDeBruijn.context β)) ⟶ J.obj (M.obj A) :=
  Semantics.Categorical.denote J M (LocallyNameless.ToDeBruijn.eraseTm_hasType h)

theorem denoteLocallyNamelessTm_commutes
    {β : LocallyNameless.BoundCtx τ n} {t : LocallyNameless.Tm Empty Φ n}
    (h : LocallyNameless.Tm.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    denoteLocallyNamelessTm J M h =
      Semantics.Categorical.denote J M (LocallyNameless.ToDeBruijn.eraseTm_hasType h) := rfl

def LocallyNamelessRegionDenotes
    {β : LocallyNameless.BoundCtx τ n} {δ : LocallyNameless.BoundCtx τ l}
    {r : LocallyNameless.Region Empty Empty Φ n l}
    (h : LocallyNameless.Region.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β δ r)
    (f : J.obj (Semantics.Categorical.ctxObj M
      (LocallyNameless.ToDeBruijn.context β)) ⟶
      J.obj (Semantics.Categorical.labelObj M
        (LocallyNameless.ToDeBruijn.context δ))) : Prop :=
  Semantics.Categorical.RegionDenotes J M
    (LocallyNameless.ToDeBruijn.eraseRegion_hasType h) f

theorem locallyNamelessRegionDenotes_commutes {β : LocallyNameless.BoundCtx τ n}
    {δ : LocallyNameless.BoundCtx τ l} {r : LocallyNameless.Region Empty Empty Φ n l}
    (h : LocallyNameless.Region.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β δ r) (f) :
    LocallyNamelessRegionDenotes J M h f ↔
      Semantics.Categorical.RegionDenotes J M
        (LocallyNameless.ToDeBruijn.eraseRegion_hasType h) f := Iff.rfl

noncomputable def denoteNamedTm {t : Named.Tm Empty Φ} (h : Named.Tm.HasType
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) t A) :
    J.obj (Semantics.Categorical.ctxObj M []) ⟶ J.obj (M.obj A) :=
  denoteLocallyNamelessTm J M
    (Named.ToLocallyNameless.translateTm_hasType (.nil) h)

theorem denoteNamedTm_commutes {t : Named.Tm Empty Φ} (h : Named.Tm.HasType
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) t A) :
    denoteNamedTm J M h = denoteLocallyNamelessTm J M
      (Named.ToLocallyNameless.translateTm_hasType (.nil) h) := rfl

def NamedRegionDenotes {r : Named.Region Empty Empty Φ} (h : Named.Region.HasType
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) r
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ))
    (f : J.obj (Semantics.Categorical.ctxObj M []) ⟶
      J.obj (Semantics.Categorical.labelObj M [])) : Prop :=
  LocallyNamelessRegionDenotes J M
    (Named.ToLocallyNameless.translateRegion_hasType
      (ρ := .nil) (ls := .nil) (β := .nil) (δ := .nil) (.nil)
      emptyLabelAlignment h) f

theorem namedRegionDenotes_commutes {r : Named.Region Empty Empty Φ}
    (h : Named.Region.HasType
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) r
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)) (f) :
    NamedRegionDenotes J M h f ↔ LocallyNamelessRegionDenotes J M
      (Named.ToLocallyNameless.translateRegion_hasType
        (ρ := .nil) (ls := .nil) (β := .nil) (δ := .nil) (.nil)
        emptyLabelAlignment h) f := Iff.rfl

end Categorical

namespace Monadic

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
  [InstructionModel Φ τ ε m]

noncomputable def denoteLocallyNamelessTm
    {β : LocallyNameless.BoundCtx τ n} {t : LocallyNameless.Tm Empty Φ n}
    (h : LocallyNameless.Tm.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    Semantics.Monadic.Env (LocallyNameless.ToDeBruijn.context β) →
      m (TyDen A) :=
  Semantics.Monadic.denote (m := m) ε (LocallyNameless.ToDeBruijn.eraseTm_hasType h)

theorem denoteLocallyNamelessTm_commutes
    {β : LocallyNameless.BoundCtx τ n} {t : LocallyNameless.Tm Empty Φ n}
    (h : LocallyNameless.Tm.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    denoteLocallyNamelessTm (ε := ε) (m := m) h =
      Semantics.Monadic.denote (m := m) ε
        (LocallyNameless.ToDeBruijn.eraseTm_hasType h) := rfl

noncomputable def denoteNamedTm {t : Named.Tm Empty Φ} (h : Named.Tm.HasType
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) t A) :
    Semantics.Monadic.Env ([] : List τ) → m (TyDen A) :=
  denoteLocallyNamelessTm (ε := ε) (m := m)
    (Named.ToLocallyNameless.translateTm_hasType (.nil) h)

theorem denoteNamedTm_commutes {t : Named.Tm Empty Φ} (h : Named.Tm.HasType
    (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) t A) :
    denoteNamedTm (ε := ε) (m := m) h =
      denoteLocallyNamelessTm (ε := ε) (m := m)
        (Named.ToLocallyNameless.translateTm_hasType (.nil) h) := rfl

end Monadic

end Isotope.LambdaSSA.Semantics.RepresentationAgreement
