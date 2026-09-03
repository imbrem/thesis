import Isotope.LambdaSSA.LocallyNameless.ToDeBruijn.Typing
import Isotope.LambdaSSA.Subtyping.LocallyNameless.Typing
import Isotope.LambdaSSA.Subtyping.Typing

namespace Isotope.LambdaSSA.Subtyping.LocallyNameless.ToDeBruijn

open Isotope.LambdaSSA
open Isotope.LambdaSSA.LocallyNameless.ToDeBruijn

noncomputable def eraseTm_hasType [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
    [LambdaIter.HasTy Φ τ]
    {β : LambdaSSA.LocallyNameless.BoundCtx τ n}
    {t : LambdaSSA.LocallyNameless.Tm Empty Φ n}
    (h : Subtyping.LocallyNameless.Tm.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    Subtyping.Tm.HasType (context β) (eraseTm t) A := by
  induction h with
  | fv h => cases h
  | bv => exact .var (getElem_context _ _)
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => exact .pair iha ihb
  | unit => exact .unit
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | sub _ d ih => exact .sub ih d

noncomputable def eraseRegion_hasType [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
    [LambdaIter.HasTy Φ τ]
    {β : LambdaSSA.LocallyNameless.BoundCtx τ n}
    {δ : LambdaSSA.LocallyNameless.BoundCtx τ l}
    {r : LambdaSSA.LocallyNameless.Region Empty Empty Φ n l}
    (h : Subtyping.LocallyNameless.Region.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β δ r) :
    Subtyping.Region.HasType (context β) (eraseRegion r) (context δ) := by
  induction h with
  | br_free h => cases h
  | br_bound harg => exact .br (getElem_context _ _) (eraseTm_hasType harg)
  | case hdiscr _ _ ihr ihs => exact .case (eraseTm_hasType hdiscr) ihr ihs
  | let₁ hvalue _ ihr => exact .let₁ (eraseTm_hasType hvalue) ihr
  | let₂ hvalue _ ihr => exact .let₂ (eraseTm_hasType hvalue) ihr
  | cfg R _ _ ihe ihbs =>
      apply Subtyping.Region.HasType.cfg R
      · simpa using ihe
      · intro i
        simpa using ihbs i

end Isotope.LambdaSSA.Subtyping.LocallyNameless.ToDeBruijn
