import Isotope.CategoryTheory.Freyd.EffectfulElgot
import Isotope.LambdaIter.Subtyping.Semantics.Categorical

/-!
# Effect soundness of the categorical semantics

The categorical semantics of `Isotope.LambdaIter.Semantics.Categorical` interprets a term as a
computation morphism.  Working in the effectful presentation of a Freyd category — a lattice of
wide subcategories `C_ε ⊆ C` indexed by effects — we can say *which* subcategory that morphism
lands in.

The main theorem, `denote_mem_eff`, says that a term whose instructions all have effect below
`ε`, and which iterates only when `ε` is closed under iteration, denotes a morphism of `C_ε`.
Specialised to `ε = ⊥` this says pure terms denote pure morphisms.

The effect model is layered to match the fragments: `EffectModel` needs only a Freyd category
and suffices for λ-seq; `DistributiveEffectModel` adds branching and suffices for λ-case;
`CategoryTheory.IterativeEffects` adds iteration for λ-iter.  The corresponding soundness
theorems live in `Isotope.LambdaSeq.Effects` and `Isotope.LambdaCase.Semantics.Effects`.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

namespace Isotope.LambdaIter.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.EffectLattice
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory

section EffectModel

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]

/-- An effect structure on the computation category of a categorical λ-iter model: a monotone
family of wide symmetric premonoidal subcategories `C_ε`, whose bottom member contains the image
of `J` together with the coherence and coproduct-splitting isomorphisms used by the semantics,
and each of which is closed under case analysis and — when `ε` is iterative — under iteration.

Together with `CategoryTheory.EffectfulFreydCategory` this is the "third semantics": the value
category is not a separate category but the subcategory `C_⊥`. -/
class EffectModel (E : Type u₅) [Preorder E] [OrderBot E]
    (J : Functor V C) [FreydCategory J]
    (eff : E → MorphismProperty C) [EffectLattice E eff] : Prop where
  /-- Value morphisms are pure. -/
  map_mem {X Y : V} (f : X ⟶ Y) : eff ⊥ (J.map f)
  /-- The coherence isomorphisms of `J` are pure. -/
  tensorIso_hom_mem (X Y : V) :
    eff ⊥ (Functor.StrongPremonoidal.tensorIso (J := J) X Y).hom
  tensorIso_inv_mem (X Y : V) :
    eff ⊥ (Functor.StrongPremonoidal.tensorIso (J := J) X Y).inv

/-- The extra structure needed to interpret branching: case analysis stays inside an effect.

The law is stated for the *composite* `splitMapCoprod ≫ coprod.desc` that the semantics
actually forms, and not for its two factors separately.  This is deliberate: `splitMapCoprod`
lands in Mathlib's globally chosen coproduct, and a chosen colimit cocone is determined only up
to twisting by an arbitrary automorphism of its apex — so neither factor has a well-determined
effect, while their composite does. -/
class DistributiveEffectModel (E : Type u₅) [Preorder E] [OrderBot E]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    (J : Functor V C) [DistributiveFreydCategory J]
    (eff : E → MorphismProperty C) [EffectLattice E eff] [EffectModel E J eff] : Prop where
  /-- Case analysis stays inside an effect. -/
  splitDesc_mem {e : E} {A B : V} {D : C} {l : J.obj A ⟶ D} {r : J.obj B ⟶ D} :
    eff e l → eff e r → eff e (splitMapCoprod J A B ≫ coprod.desc l r)

namespace EffectModel

variable {E : Type u₅} [Preorder E] [OrderBot E]
  {J : Functor V C} [FreydCategory J]
  {eff : E → MorphismProperty C} [EffectLattice E eff] [EffectModel E J eff]

theorem pure_mem {X Y : C} {f : X ⟶ Y} (hf : eff ⊥ f) (e : E) : eff e f :=
  EffectLattice.eff_mono (eff := eff) bot_le _ hf

theorem id_mem (e : E) (X : C) : eff e (𝟙 X) := MorphismProperty.id_mem _ _

theorem mono_mem {e e' : E} (h : e ≤ e') {X Y : C} {f : X ⟶ Y} (hf : eff e f) : eff e' f :=
  EffectLattice.eff_mono (eff := eff) h _ hf

theorem comp_mem {e : E} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : eff e f) (hg : eff e g) : eff e (f ≫ g) :=
  MorphismProperty.comp_mem _ _ _ hf hg

theorem map_mem_eff (e : E) {X Y : V} (f : X ⟶ Y) : eff e (J.map f) :=
  pure_mem (EffectModel.map_mem (J := J) (eff := eff) f) e

theorem whiskerLeft_mem {e : E} (Z : C) {X Y : C} {f : X ⟶ Y} (hf : eff e f) :
    eff e (Z ◁ f) := IsPremonoidalSubcategory.whiskerLeft_mem Z hf

theorem whiskerRight_mem {e : E} {X Y : C} {f : X ⟶ Y} (hf : eff e f) (Z : C) :
    eff e (f ▷ Z) := IsPremonoidalSubcategory.whiskerRight_mem Z hf

theorem leftTensor_id_mem {e : E} (R : C) {X Y : C} {f : X ⟶ Y} (hf : eff e f) :
    eff e (leftTensor (𝟙 R) f) :=
  comp_mem (whiskerRight_mem (id_mem e R) _) (whiskerLeft_mem R hf)

theorem extend_mem {e : E} {R A : V} {f : J.obj R ⟶ J.obj A} (hf : eff e f) :
    eff e (extend J f) :=
  comp_mem (map_mem_eff e _)
    (comp_mem (pure_mem (EffectModel.tensorIso_inv_mem (J := J) (eff := eff) R R) e)
      (comp_mem (leftTensor_id_mem _ hf)
        (pure_mem (EffectModel.tensorIso_hom_mem (J := J) (eff := eff) R A) e)))

theorem bind_mem {e : E} {R A B : V} {f : J.obj R ⟶ J.obj A} {g : J.obj (R ⊗ A) ⟶ J.obj B}
    (hf : eff e f) (hg : eff e g) : eff e (bind J f g) :=
  comp_mem (extend_mem hf) hg

theorem retainedContext_mem (e : E) {R A : V} : eff e (retainedContext J (R := R) (A := A)) :=
  map_mem_eff e _

theorem pair_mem {e : E} {R A B : V} {f : J.obj R ⟶ J.obj A} {g : J.obj R ⟶ J.obj B}
    (hf : eff e f) (hg : eff e g) : eff e (pair J f g) :=
  bind_mem hf (bind_mem (comp_mem (retainedContext_mem e) hg) (map_mem_eff e _))

end EffectModel

namespace EffectModel

section Distributive

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {E : Type u₅} [Preorder E] [OrderBot E]
  {J : Functor V C} [DistributiveFreydCategory J]
  {eff : E → MorphismProperty C} [EffectLattice E eff] [EffectModel E J eff]
  [DistributiveEffectModel E J eff]

theorem caseWithContext_mem {e : E} {R A B D : V}
    {scrutinee : J.obj R ⟶ J.obj (A ⨿ B)}
    {left : J.obj (R ⊗ A) ⟶ J.obj D} {right : J.obj (R ⊗ B) ⟶ J.obj D}
    (hs : eff e scrutinee) (hl : eff e left) (hr : eff e right) :
    eff e (caseWithContext J scrutinee left right) :=
  bind_mem hs
    (comp_mem (map_mem_eff e _)
      (DistributiveEffectModel.splitDesc_mem (J := J) (eff := eff) hl hr))

theorem abort_mem {τ : Type u₃} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)
    {e : E} {R : V} {A : τ} {c : J.obj R ⟶ J.obj (M.obj (TypeFormers.empty : τ))} (hc : eff e c) :
    eff e (abort J M (A := A) c) := comp_mem hc (map_mem_eff e _)

end Distributive

section Elgot

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  {E : Type u₅} [Preorder E] [OrderBot E]
  {J : Functor V C} [StrongElgotFreydCategory J]
  {eff : E → MorphismProperty C} [EffectLattice E eff] [EffectModel E J eff]
  [DistributiveEffectModel E J eff]

theorem retainLeft_mem {e : E} {R X Y : V} {f : J.obj X ⟶ J.obj Y} (hf : eff e f) :
    eff e (retainLeft J (R := R) f) :=
  comp_mem (pure_mem (EffectModel.tensorIso_inv_mem (J := J) (eff := eff) R X) e)
    (comp_mem (leftTensor_id_mem _ hf)
      (pure_mem (EffectModel.tensorIso_hom_mem (J := J) (eff := eff) R Y) e))

theorem contextualLoop_mem {iterative : E → Prop} [IterativeEffects E J eff iterative]
    {e : E} (he : iterative e)
    {R A B : V} {body : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)} (hb : eff e body) :
    eff e (contextualLoop J body) := by
  rw [contextualLoop, ← Category.assoc, ← Category.assoc]
  exact comp_mem
    (IterativeEffects.iterate_mem (J := J) (eff := eff) he
      (comp_mem (comp_mem (map_mem_eff e _) (retainLeft_mem hb)) (map_mem_eff e _)))
    (map_mem_eff e _)

end Elgot

end EffectModel

/-! ### Consistency

The degenerate one-effect system, in which every morphism is allowed, satisfies every axiom
above; the soundness theorem below is therefore not vacuous. -/

section Consistency

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]

instance topEffectLattice :
    EffectLattice PUnit (fun _ : PUnit => (⊤ : MorphismProperty C)) where
  eff_mono _ _ _ := le_rfl
  eff_subcategory _ := inferInstanceAs (IsSymmetricSubcategory (⊤ : MorphismProperty C))

instance topEffectModel :
    EffectModel PUnit J (fun _ : PUnit => (⊤ : MorphismProperty C)) where
  map_mem _ := trivial
  tensorIso_hom_mem _ _ := trivial
  tensorIso_inv_mem _ _ := trivial

instance topDistributiveEffectModel :
    DistributiveEffectModel PUnit J (fun _ : PUnit => (⊤ : MorphismProperty C)) where
  splitDesc_mem _ _ := trivial

instance topIterativeEffects :
    IterativeEffects PUnit J (fun _ : PUnit => (⊤ : MorphismProperty C))
      (fun _ => True) where
  iterate_mem := by intros; trivial

end Consistency

/-! ### Effect soundness -/

open LocallyNameless in
/-- Primitive instructions denote morphisms of the effect they declare.  This needs no more
than a Freyd category: it is shared by λ-seq, λ-case and λ-iter. -/
class EffectfulInstructionModel (E : Type u₅) [Preorder E] [OrderBot E]
    [HasFiniteCoproducts V]
    (J : Functor V C) [FreydCategory J]
    (eff : E → MorphismProperty C) [EffectLattice E eff] [EffectModel E J eff]
    {τ : Type u₃} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)
    (Φ : Type u₄) [HasTy Φ τ] [HasEff Φ E] [InstructionModel J M Φ] : Prop where
  denote_mem (f : Φ) :
    eff (instrEff f) (InstructionModel.denote (J := J) (M := M) f)

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]

section Soundness

open EffectModel LocallyNameless

variable {E : Type u₅} [Preorder E] [OrderBot E]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {eff : E → MorphismProperty C} [EffectLattice E eff] [EffectModel E J eff]
  [DistributiveEffectModel E J eff]
  {τ : Type u₃} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₄} [HasTy Φ τ] [HasEff Φ E] [InstructionModel J M Φ]
  [EffectfulInstructionModel E J eff M Φ]
  {iterative : E → Prop} [IterativeEffects E J eff iterative]

/-- **Effect soundness of the categorical semantics.**

If every instruction of `t` has effect below `ε`, and `t` iterates only when `ε` is closed under
iteration, then the denotation of any typing derivation of `t` is a morphism of `C_ε`.

Specialising `ε` to `⊥` says that the pure fragment denotes pure morphisms.  The λ-seq and
λ-case fragments get their own statements, under correspondingly weaker hypotheses, in
`Isotope.LambdaSeq.Effects` and `Isotope.LambdaCase.Semantics.Effects`. -/
theorem denote_mem_eff {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {t : LocallyNameless.Tm ν Φ n} {A : τ} {e : E}
    (h : HasType Φ Γ β t A) (he : HasEffect iterative e t) :
    eff e (denote J M h) := by
  induction h with
  | fv _ => simp only [denote]; exact map_mem_eff e _
  | bv => simp only [denote]; exact map_mem_eff e _
  | op ha ih =>
      cases he with
      | op hf hea =>
          simp only [denote]
          exact comp_mem (ih hea)
            (mono_mem hf (EffectfulInstructionModel.denote_mem (E := E) (J := J) (M := M) _))
  | let₁ ha hb iha ihb =>
      cases he with
      | let₁ hea heb =>
          simp only [denote]
          exact bind_mem (iha hea) (comp_mem (map_mem_eff e _) (ihb heb))
  | unit => simp only [denote]; exact map_mem_eff e _
  | pair ha hb iha ihb =>
      cases he with
      | pair hea heb =>
          simp only [denote]
          exact comp_mem (pair_mem (iha hea) (ihb heb)) (map_mem_eff e _)
  | let₂ ha hc iha ihc =>
      cases he with
      | let₂ hea hec =>
          simp only [denote]
          exact bind_mem (iha hea)
            (comp_mem (map_mem_eff e _) (comp_mem (map_mem_eff e _) (ihc hec)))
  | inl ha ih =>
      cases he with
      | inl hea => simp only [denote]; exact comp_mem (ih hea) (map_mem_eff e _)
  | inr hb ih =>
      cases he with
      | inr heb => simp only [denote]; exact comp_mem (ih heb) (map_mem_eff e _)
  | case hc hl hr ihc ihl ihr =>
      cases he with
      | case hec hel her =>
          simp only [denote]
          exact caseWithContext_mem (comp_mem (ihc hec) (map_mem_eff e _))
            (comp_mem (map_mem_eff e _) (ihl hel))
            (comp_mem (map_mem_eff e _) (ihr her))
  | abort ha ih =>
      cases he with
      | abort hea => simp only [denote]; exact abort_mem M (ih hea)
  | iter ha hb iha ihb =>
      cases he with
      | iter hi hea heb =>
          simp only [denote]
          exact bind_mem (iha hea)
            (contextualLoop_mem hi
              (comp_mem (map_mem_eff e _) (comp_mem (ihb heb) (map_mem_eff e _))))
  | sub ha d ih => simp only [denote]; exact comp_mem (ih he) (map_mem_eff e _)

end Soundness

end EffectModel

/-! ### The third semantics

Instantiating everything at the inclusion of the pure morphisms.  There is no separate value
category: `V = C_⊥`, and the effect of a term is read off directly as membership in `C_ε`. -/

section SubcategoryPresentation

open CategoryTheory.EffectfulFreydCategory LocallyNameless

variable {E : Type u₅} [Preorder E] [OrderBot E]
  {C : Type u₂} [Category.{v₂} C] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [CocartesianMonoidalCategory C] [DistributiveTensor C] [Iteration C] [ElgotCategory C]
  [IsStrongIteration C]
  (eff : E → MorphismProperty C)
  [IsCentralSubcategory (eff ⊥)] [IsSemiCartesianSubcategory (eff ⊥)]
  [IsCartesianSubcategory (eff ⊥)] [EffectfulFreydCategory E eff]
  [IsCocartesianEffectLattice E eff] [IsDistributiveSubcategory (eff ⊥)]
  [IsUniformIteration (eff ⊥)]

/-- **The effect lattice of an Elgot effectful Freyd category is an effect model for its own
pure inclusion.**  This is what makes the soundness theorem apply to the subcategory
presentation. -/
instance inclusionEffectModel : EffectModel E (EffectfulFreydCategory.inclusion eff) eff where
  map_mem f := f.2
  tensorIso_hom_mem _ _ := MorphismProperty.id_mem _ _
  tensorIso_inv_mem _ _ := MorphismProperty.id_mem _ _

omit [DistributiveTensor C] [Iteration C] [ElgotCategory C] [IsStrongIteration C]
  [IsDistributiveSubcategory (eff ⊥)] in
open CocartesianMonoidalCategory in
/-- The chosen left injection of `C`, followed by the comparison with Mathlib's coproduct in the
pure subcategory, is the pure subcategory's own left injection. -/
private theorem inl_wideCoprodIso' (A B : EffectfulFreydCategory.Value eff) :
    inl A.obj B.obj ≫ (wideCoprodIso (eff ⊥) A B).hom = (coprod.inl : A ⟶ A ⨿ B).1 :=
  congrArg Subtype.val
    ((wideBinaryCofanIsColimit (eff ⊥) A B).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (Limits.pair A B)) (Discrete.mk WalkingPair.left))

omit [DistributiveTensor C] [Iteration C] [ElgotCategory C] [IsStrongIteration C]
  [IsDistributiveSubcategory (eff ⊥)] in
open CocartesianMonoidalCategory in
/-- The right injection, likewise. -/
private theorem inr_wideCoprodIso' (A B : EffectfulFreydCategory.Value eff) :
    inr A.obj B.obj ≫ (wideCoprodIso (eff ⊥) A B).hom = (coprod.inr : B ⟶ A ⨿ B).1 :=
  congrArg Subtype.val
    ((wideBinaryCofanIsColimit (eff ⊥) A B).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (Limits.pair A B)) (Discrete.mk WalkingPair.right))

omit [Iteration C] [ElgotCategory C] [IsStrongIteration C] [IsUniformIteration (eff ⊥)] in
open CocartesianMonoidalCategory in
/-- Splitting the image of a pure coproduct and then copairing is the same as comparing with the
*chosen* coproduct of `C` and copairing there.  Neither factor on the left has a well-determined
effect, but this composite does. -/
private theorem splitMapCoprod_desc_eq {A B : EffectfulFreydCategory.Value eff} {D : C}
    (l : (EffectfulFreydCategory.inclusion eff).obj A ⟶ D)
    (r : (EffectfulFreydCategory.inclusion eff).obj B ⟶ D) :
    splitMapCoprod (EffectfulFreydCategory.inclusion eff) A B ≫ coprod.desc l r =
      (wideCoprodIso (eff ⊥) A B).inv ≫ desc l r := by
  rw [splitMapCoprod, IsIso.inv_comp_eq]
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc, coprodComparison_inl_assoc]
    change l = (coprod.inl : A ⟶ A ⨿ B).1 ≫ (wideCoprodIso (eff ⊥) A B).inv ≫ desc l r
    rw [← inl_wideCoprodIso' eff A B, Category.assoc, Iso.hom_inv_id_assoc, inl_desc]
  · rw [coprod.inr_desc, coprodComparison_inr_assoc]
    change r = (coprod.inr : B ⟶ A ⨿ B).1 ≫ (wideCoprodIso (eff ⊥) A B).inv ≫ desc l r
    rw [← inr_wideCoprodIso' eff A B, Category.assoc, Iso.hom_inv_id_assoc, inr_desc]

instance inclusionDistributiveEffectModel :
    DistributiveEffectModel E (EffectfulFreydCategory.inclusion eff) eff where
  splitDesc_mem hl hr := by
    rw [splitMapCoprod_desc_eq]
    exact MorphismProperty.comp_mem _ _ _
      (EffectLattice.eff_mono (eff := eff) bot_le _ (wideCoprodIso_inv_mem (eff ⊥) _ _))
      (IsCocartesianSubcategory.desc_mem hl hr)

variable {τ : Type u₃} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ (EffectfulFreydCategory.Value eff))
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₄} [HasTy Φ τ] [HasEff Φ E] [InstructionModel (EffectfulFreydCategory.inclusion eff) M Φ]
  [EffectfulInstructionModel E (EffectfulFreydCategory.inclusion eff) eff M Φ]
  {iterative : E → Prop}
  [IterativeEffects E (EffectfulFreydCategory.inclusion eff) eff iterative]

/-- **Effect soundness for the subcategory presentation.**

Interpreting λ-iter in an Elgot effectful Freyd category, whose value category is the
subcategory `C_⊥ ⊆ C` of pure morphisms, a term whose instructions all have effect below `ε` and
which iterates only at iterative effects denotes a morphism of `C_ε`. -/
theorem denote_mem_eff_pure {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {t : LocallyNameless.Tm ν Φ n} {A : τ} {e : E}
    (h : HasType Φ Γ β t A) (he : HasEffect iterative e t) :
    eff e (denote (EffectfulFreydCategory.inclusion eff) M h) :=
  denote_mem_eff (EffectfulFreydCategory.inclusion eff) M h he

end SubcategoryPresentation

end Isotope.LambdaIter.Subtyping.Semantics.Categorical
