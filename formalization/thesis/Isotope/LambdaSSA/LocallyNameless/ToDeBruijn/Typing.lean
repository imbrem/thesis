import Isotope.LambdaSSA.LocallyNameless.ToDeBruijn
import Isotope.LambdaSSA.LocallyNameless.Typing
import Isotope.LambdaSSA.Typing

/-! # Typing for the closed locally nameless/de Bruijn bridge -/

namespace Isotope.LambdaSSA.LocallyNameless.ToDeBruijn

def context : LocallyNameless.BoundCtx τ n → List τ
  | .nil => []
  | .snoc β A => A :: context β

@[simp] theorem context_snoc (β : LocallyNameless.BoundCtx τ n) (A : τ) :
    context (.snoc β A) = A :: context β := rfl

@[simp] theorem context_ofFin : {n : Nat} → (f : Fin n → τ) →
    context (LambdaIter.LocallyNameless.BoundCtx.ofFin f) = List.ofFn f
  | 0, _ => rfl
  | n + 1, f => by
      simp [LambdaIter.LocallyNameless.BoundCtx.ofFin, context,
        List.ofFn_succ, context_ofFin]

@[simp] theorem context_extendLabelCtx (δ : LocallyNameless.BoundCtx τ l)
    {arity : Nat} (R : Fin arity → τ) :
    context (LocallyNameless.extendLabelCtx δ R) = List.ofFn R ++ context δ := by
  rw [LocallyNameless.extendLabelCtx, context_ofFin, List.ofFn_add]
  congr 1
  · rw [List.ofFn_inj]
    funext i
    rw [show Fin.castLE (Nat.le_add_right arity l) i = Fin.castAdd l i by
      apply Fin.ext; rfl]
    rw [Fin.addCases_left]
  · simpa using (context_ofFin δ.get).symm

@[simp] theorem getElem_context (β : LocallyNameless.BoundCtx τ n) (i : Fin n) :
    (context β)[i.val]? = some (β.get i) := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases rfl (fun j => ?_) i
      simpa [context, LambdaIter.LocallyNameless.BoundCtx.get] using ih j

def eraseTm_hasType [LambdaIter.TypeFormers τ] [LambdaIter.HasTy Φ τ]
    {β : LocallyNameless.BoundCtx τ n} {t : LocallyNameless.Tm Empty Φ n}
    (h : LocallyNameless.Tm.HasType Φ (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      β t A) : LambdaSSA.Tm.HasType (context β) (eraseTm t) A := by
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

def eraseRegion_hasType [LambdaIter.TypeFormers τ] [LambdaIter.HasTy Φ τ]
    {β : LocallyNameless.BoundCtx τ n} {δ : LocallyNameless.BoundCtx τ l}
    {r : LocallyNameless.Region Empty Empty Φ n l}
    (h : LocallyNameless.Region.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β δ r) :
    LambdaSSA.Region.HasType (context β) (eraseRegion r) (context δ) := by
  induction h with
  | br_free h => cases h
  | br_bound harg => exact .br (getElem_context _ _) (eraseTm_hasType harg)
  | case hdiscr _ _ ihr ihs => exact .case (eraseTm_hasType hdiscr) ihr ihs
  | let₁ hvalue _ ihr => exact .let₁ (eraseTm_hasType hvalue) ihr
  | let₂ hvalue _ ihr => exact .let₂ (eraseTm_hasType hvalue) ihr
  | cfg R _ _ ihe ihbs =>
      apply LambdaSSA.Region.HasType.cfg R
      · simpa using ihe
      · intro i
        simpa using ihbs i

theorem embedTm_hasType [LambdaIter.TypeFormers τ] [LambdaIter.HasTy Φ τ]
    {t : LambdaSSA.Tm Φ} (hs : Tm.Scoped n t)
    (h : LambdaSSA.Tm.HasType (context β) t A) :
    Nonempty (LocallyNameless.Tm.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β (embedTm hs) A) := by
  induction hs generalizing A with
  | var i =>
      cases h with
      | var hAt =>
          have hty : β.get i = A := by
            have := getElem_context β i
            simp_all
          exact ⟨hty ▸ .bv⟩
  | op hs ih => cases h with | op h => exact ⟨.op (Classical.choice (ih h))⟩
  | let₁ ha hb iha ihb => cases h with
      | let₁ hta htb => exact ⟨.let₁ (Classical.choice (iha hta)) (Classical.choice (ihb htb))⟩
  | pair ha hb iha ihb => cases h with
      | pair hta htb => exact ⟨.pair (Classical.choice (iha hta)) (Classical.choice (ihb htb))⟩
  | unit => cases h; exact ⟨.unit⟩
  | let₂ ha hb iha ihb => cases h with
      | let₂ hta htb => exact ⟨.let₂ (Classical.choice (iha hta)) (Classical.choice (ihb htb))⟩
  | inl hs ih => cases h with | inl h => exact ⟨.inl (Classical.choice (ih h))⟩
  | inr hs ih => cases h with | inr h => exact ⟨.inr (Classical.choice (ih h))⟩
  | case he hl hr ihe ihl ihr => cases h with
      | case hte htl htr => exact ⟨.case (Classical.choice (ihe hte))
          (Classical.choice (ihl htl)) (Classical.choice (ihr htr))⟩
  | abort hs ih => cases h with | abort h => exact ⟨.abort (Classical.choice (ih h))⟩

theorem embedRegion_hasType [LambdaIter.TypeFormers τ] [LambdaIter.HasTy Φ τ]
    {r : LambdaSSA.Region Φ} (hs : Region.Scoped n l r)
    (h : LambdaSSA.Region.HasType (context β) r (context δ)) :
    Nonempty (LocallyNameless.Region.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β δ (embedRegion hs)) := by
  induction hs with
  | br i hs =>
      cases h with
      | br hAt harg =>
          have hty := Option.some.inj ((getElem_context δ i).symm.trans hAt)
          exact ⟨.br_bound (hty ▸ Classical.choice (embedTm_hasType hs harg))⟩
  | case ha hr hs ihr ihs => cases h with
      | case harg hleft hright => exact ⟨.case (Classical.choice (embedTm_hasType ha harg))
          (Classical.choice (ihr hleft)) (Classical.choice (ihs hright))⟩
  | let₁ ha hr ihr => cases h with
      | let₁ harg hbody => exact ⟨.let₁ (Classical.choice (embedTm_hasType ha harg))
          (Classical.choice (ihr hbody))⟩
  | let₂ ha hr ihr => cases h with
      | let₂ harg hbody => exact ⟨.let₂ (Classical.choice (embedTm_hasType ha harg))
          (Classical.choice (ihr hbody))⟩
  | cfg hsentry hsblocks ihentry ihblocks => cases h with
      | cfg R hentry hblocks =>
          exact ⟨.cfg R (Classical.choice (ihentry (by simpa using hentry)))
            (fun i => Classical.choice (ihblocks i (by simpa using hblocks i)))⟩

end Isotope.LambdaSSA.LocallyNameless.ToDeBruijn
