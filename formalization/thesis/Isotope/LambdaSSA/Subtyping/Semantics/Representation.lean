import Isotope.LambdaSSA.Subtyping.Named.ToLocallyNameless.Typing
import Isotope.LambdaSSA.Subtyping.LocallyNameless.ToDeBruijn.Typing
import Isotope.LambdaSSA.Subtyping.Semantics.Agreement.Region

/-! # Semantics of named and locally nameless proof-relevant SSA -/

namespace Isotope.LambdaSSA.Subtyping.Semantics.Representation

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]

private abbrev J := CategoryTheory.Kleisli.Adjunction.toKleisli
  (CategoryTheory.ofTypeMonad m)
private noncomputable abbrev M :=
  Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofTypeModel (τ := τ)

namespace LocallyNameless

noncomputable def denoteTm
    {β : LambdaSSA.LocallyNameless.BoundCtx τ n}
    {t : LambdaSSA.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaSSA.Subtyping.LocallyNameless.Tm.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    LambdaSSA.Subtyping.Semantics.Monadic.Env
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) → m (TyDen A) :=
  LambdaSSA.Subtyping.Semantics.Monadic.denote (ε := ε) (m := m)
    (LambdaSSA.Subtyping.LocallyNameless.ToDeBruijn.eraseTm_hasType h)

noncomputable def denoteRegion
    {β : LambdaSSA.LocallyNameless.BoundCtx τ n}
    {δ : LambdaSSA.LocallyNameless.BoundCtx τ l}
    {region : LambdaSSA.LocallyNameless.Region Empty Empty Φ n l}
    (h : LambdaSSA.Subtyping.LocallyNameless.Region.HasType Φ
      (Ctx.nil : Ctx Empty τ) (Ctx.nil : Ctx Empty τ) β δ region) :
    LambdaSSA.Subtyping.Semantics.Monadic.Env
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) →
      m (LambdaSSA.Subtyping.Semantics.Monadic.LabelDen
        (LambdaSSA.LocallyNameless.ToDeBruijn.context δ)) :=
  LambdaSSA.Subtyping.Semantics.Monadic.denoteRegion (ε := ε) (m := m)
    (LambdaSSA.Subtyping.LocallyNameless.ToDeBruijn.eraseRegion_hasType h)

noncomputable def denoteTmCategorical
    {β : LambdaSSA.LocallyNameless.BoundCtx τ n}
    {t : LambdaSSA.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaSSA.Subtyping.LocallyNameless.Tm.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :=
  letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  LambdaSSA.Subtyping.Semantics.Categorical.denote (J (m := m)) (M (τ := τ))
    (LambdaSSA.Subtyping.LocallyNameless.ToDeBruijn.eraseTm_hasType h)

theorem denoteTm_categorical_agrees
    {β : LambdaSSA.LocallyNameless.BoundCtx τ n}
    {t : LambdaSSA.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : LambdaSSA.Subtyping.LocallyNameless.Tm.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A)
    (ρ : LambdaSSA.Subtyping.Semantics.Monadic.Env
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β)) :
    letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    (denoteTmCategorical (ε := ε) (m := m) h).of
        (Agreement.envToCategorical ρ) =
      denoteTm (ε := ε) (m := m) h ρ := by
  simpa [denoteTmCategorical, denoteTm] using congrFun
    (Agreement.denote_agrees
      (ε := ε) (m := m)
      (LambdaSSA.Subtyping.LocallyNameless.ToDeBruijn.eraseTm_hasType h)) ρ

noncomputable def denoteRegionCategorical
    {β : LambdaSSA.LocallyNameless.BoundCtx τ n}
    {δ : LambdaSSA.LocallyNameless.BoundCtx τ l}
    {region : LambdaSSA.LocallyNameless.Region Empty Empty Φ n l}
    (h : LambdaSSA.Subtyping.LocallyNameless.Region.HasType Φ
      (Ctx.nil : Ctx Empty τ) (Ctx.nil : Ctx Empty τ) β δ region) :=
  letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  LambdaSSA.Subtyping.Semantics.Categorical.denoteRegion
    (J (m := m)) (M (τ := τ))
    (LambdaSSA.Subtyping.LocallyNameless.ToDeBruijn.eraseRegion_hasType h)

theorem denoteRegion_categorical_agrees
    (coherent : Agreement.RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {β : LambdaSSA.LocallyNameless.BoundCtx τ n}
    {δ : LambdaSSA.LocallyNameless.BoundCtx τ l}
    {region : LambdaSSA.LocallyNameless.Region Empty Empty Φ n l}
    (h : LambdaSSA.Subtyping.LocallyNameless.Region.HasType Φ
      (Ctx.nil : Ctx Empty τ) (Ctx.nil : Ctx Empty τ) β δ region)
    (ρ : LambdaSSA.Subtyping.Semantics.Monadic.Env
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β)) :
    letI := Isotope.LambdaIter.Subtyping.Semantics.Categorical.ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    (denoteRegionCategorical (ε := ε) (m := m) h).of
        (Agreement.envToCategorical ρ) =
      (denoteRegion (ε := ε) (m := m) h ρ >>= fun x => pure
        (LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv
          (LambdaSSA.LocallyNameless.ToDeBruijn.context δ) x)) := by
  simpa [denoteRegionCategorical, denoteRegion] using
    Agreement.denoteRegion_agrees coherent
      (LambdaSSA.Subtyping.LocallyNameless.ToDeBruijn.eraseRegion_hasType h) ρ

end LocallyNameless

namespace Named

private abbrev tmAligned :
    LambdaSSA.Named.ToLocallyNameless.Aligned
      (Ctx.nil : Ctx Empty τ) .nil .nil (Ctx.nil : Ctx Empty τ) :=
  .nil

private abbrev labelAligned :
  LambdaSSA.Named.ToLocallyNameless.LookupAligned
      (Ctx.nil : Ctx Empty τ) .nil .nil (Ctx.nil : Ctx Empty τ) :=
  LambdaSSA.Named.ToLocallyNameless.LookupAligned.of_aligned .nil

noncomputable def translatedTm
    {t : LambdaSSA.Named.Tm Empty Φ} {A : τ}
    (h : LambdaSSA.Subtyping.Named.Tm.HasType (Ctx.nil : Ctx Empty τ) t A) :=
  LambdaSSA.Subtyping.Named.ToLocallyNameless.translateTm_hasType tmAligned h

noncomputable def translatedRegion
    {region : LambdaSSA.Named.Region Empty Empty Φ}
    (h : LambdaSSA.Subtyping.Named.Region.HasType
      (Ctx.nil : Ctx Empty τ) region (Ctx.nil : Ctx Empty τ)) :=
  LambdaSSA.Subtyping.Named.ToLocallyNameless.translateRegion_hasType tmAligned
    (ρ := .nil) (ls := .nil) (β := .nil) (δ := .nil)
    (Γ := Ctx.nil) (K := Ctx.nil) labelAligned h

noncomputable def denoteTm
    {t : LambdaSSA.Named.Tm Empty Φ} {A : τ}
    (h : LambdaSSA.Subtyping.Named.Tm.HasType (Ctx.nil : Ctx Empty τ) t A) :
    m (TyDen A) :=
  LocallyNameless.denoteTm (ε := ε) (m := m) (translatedTm h) PUnit.unit

/-- Translating a closed named term to locally nameless SSA preserves its
proof-relevant monadic denotation definitionally. -/
theorem denoteTm_translate
    {t : LambdaSSA.Named.Tm Empty Φ} {A : τ}
    (h : LambdaSSA.Subtyping.Named.Tm.HasType (Ctx.nil : Ctx Empty τ) t A) :
    denoteTm (ε := ε) (m := m) h =
      LocallyNameless.denoteTm (ε := ε) (m := m) (translatedTm h) PUnit.unit := rfl

noncomputable def denoteTmCategorical
    {t : LambdaSSA.Named.Tm Empty Φ} {A : τ}
    (h : LambdaSSA.Subtyping.Named.Tm.HasType (Ctx.nil : Ctx Empty τ) t A) :=
  LocallyNameless.denoteTmCategorical (ε := ε) (m := m) (translatedTm h)

theorem denoteTmCategorical_translate
    {t : LambdaSSA.Named.Tm Empty Φ} {A : τ}
    (h : LambdaSSA.Subtyping.Named.Tm.HasType (Ctx.nil : Ctx Empty τ) t A) :
    denoteTmCategorical (ε := ε) (m := m) h =
      LocallyNameless.denoteTmCategorical (ε := ε) (m := m)
        (translatedTm h) := rfl

noncomputable def denoteRegion
    {region : LambdaSSA.Named.Region Empty Empty Φ}
    (h : LambdaSSA.Subtyping.Named.Region.HasType
      (Ctx.nil : Ctx Empty τ) region (Ctx.nil : Ctx Empty τ)) :
    m (@LambdaSSA.Subtyping.Semantics.Monadic.LabelDen τ _ _ _ []) :=
  LocallyNameless.denoteRegion (ε := ε) (m := m)
    (translatedRegion h) PUnit.unit

/-- The same representation square commutes for closed regions/CFGs. -/
theorem denoteRegion_translate
    {region : LambdaSSA.Named.Region Empty Empty Φ}
    (h : LambdaSSA.Subtyping.Named.Region.HasType
      (Ctx.nil : Ctx Empty τ) region (Ctx.nil : Ctx Empty τ)) :
    denoteRegion (ε := ε) (m := m) h =
      LocallyNameless.denoteRegion (ε := ε) (m := m)
        (translatedRegion h) PUnit.unit := rfl

noncomputable def denoteRegionCategorical
    {region : LambdaSSA.Named.Region Empty Empty Φ}
    (h : LambdaSSA.Subtyping.Named.Region.HasType
      (Ctx.nil : Ctx Empty τ) region (Ctx.nil : Ctx Empty τ)) :=
  LocallyNameless.denoteRegionCategorical (ε := ε) (m := m) (translatedRegion h)

theorem denoteRegionCategorical_translate
    {region : LambdaSSA.Named.Region Empty Empty Φ}
    (h : LambdaSSA.Subtyping.Named.Region.HasType
      (Ctx.nil : Ctx Empty τ) region (Ctx.nil : Ctx Empty τ)) :
    denoteRegionCategorical (ε := ε) (m := m) h =
      LocallyNameless.denoteRegionCategorical (ε := ε) (m := m)
        (translatedRegion h) := rfl

end Named

end Isotope.LambdaSSA.Subtyping.Semantics.Representation
