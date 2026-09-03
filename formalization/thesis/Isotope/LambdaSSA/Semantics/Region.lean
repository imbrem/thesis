import Isotope.LambdaSSA.Semantics.Finite
import Isotope.LambdaSSA.Semantics.Collective
import Isotope.LambdaSSA.Semantics.Inversion

/-! # Relational categorical semantics of lambda-SSA regions

This module gives the paper's equations for branches, case regions, and
straight-line bindings.  The relation is indexed by the existing extrinsic
typing derivation, just as the term semantics is.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaSSA.Semantics.Categorical

set_option autoImplicit true
set_option relaxedAutoImplicit true

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open scoped MonoidalCategory

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

noncomputable def labelAppendRoute (R L : LCtx τ)
    (i : Fin (R ++ L).length) :
    M.obj ((R ++ L).get i) ⟶ labelObj M L ⨿ labelObj M R := by
  by_cases hi : i.val < R.length
  · exact labelInject M i.val (by
      simp only [At, List.getElem?_eq_getElem, List.length_append]
      simp [hi]) ≫ coprod.inr
  · let j := i.val - R.length
    exact labelInject M j (by
      change L[j]? = some (R ++ L)[i.val]
      have ht : (R ++ L)[i.val]? = some (R ++ L)[i.val] := by simp
      rw [List.getElem?_append_right (by omega)] at ht
      simpa [j] using ht) ≫ coprod.inl

/-- Separate external from locally bound labels in an appended label context.
The local labels occur first because label contexts use de Bruijn order. -/
noncomputable def labelAppendSplit (R L : LCtx τ) :
    labelObj M (R ++ L) ⟶ labelObj M L ⨿ labelObj M R :=
  Limits.Sigma.desc (labelAppendRoute M R L)

@[reassoc (attr := simp)] theorem labelAppendSplit_ι (R L : LCtx τ)
    (i : Fin (R ++ L).length) :
    Limits.Sigma.ι (fun k : Fin (R ++ L).length => M.obj ((R ++ L).get k)) i ≫
      labelAppendSplit M R L = labelAppendRoute M R L i := by
  rw [labelAppendSplit, Limits.Sigma.ι_desc]

/-- A collective block arrow is characterized by its restriction to every
local-label summand, with the read-only SSA context carried on the left. -/
structure CollectiveDenotes (Γ : VCtx τ) {n : Nat} (R : Fin n → τ) (L : LCtx τ)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
      J.obj (labelObj M (List.ofFn R ++ L)))
    (f : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶
      J.obj (labelObj M (List.ofFn R ++ L))) : Prop where
  restrict (i : Fin n) :
    J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i) ≫ f = block i

/-- A one-block collective needs no nullary tensor-distributivity law. -/
theorem collectiveDenotes_one (Γ : VCtx τ) (R : Fin 1 → τ) (L : LCtx τ)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
      J.obj (labelObj M (List.ofFn R ++ L))) :
    ∃ f, CollectiveDenotes J M Γ R L block f := by
  rcases finiteCollective_exists_succ J M 0 Γ R _ block with ⟨f, df⟩
  exact ⟨f, ⟨df.restrict⟩⟩

/-- Every nonempty finite family of blocks has a collective arrow. -/
theorem collectiveDenotes_exists_succ (n : Nat) (Γ : VCtx τ)
    (R : Fin (n + 1) → τ) (L : LCtx τ)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
      J.obj (labelObj M (List.ofFn R ++ L))) :
    ∃ f, CollectiveDenotes J M Γ R L block f := by
  rcases finiteCollective_exists_succ J M n Γ R _ block with ⟨f, df⟩
  exact ⟨f, ⟨df.restrict⟩⟩

/-- Structural denotation graph for the non-recursive region constructors.
The absence of a `cfg` constructor is intentional: recursive CFG wiring is a
separate Elgot construction, whereas these rules require only a distributive
Freyd category. -/
inductive RegionDenotes : {Γ : VCtx τ} → {r : Region Φ} → {L : LCtx τ} →
    Region.HasType Γ r L → (J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)) → Prop where
  | br (dt : Denotes J M ha fa) :
      RegionDenotes (.br h ha) (fa ≫ J.map (labelInject M _ h))
  | case (de : Denotes J M he fe)
      (dl : RegionDenotes hl fl) (dr : RegionDenotes hr fr) :
      RegionDenotes (.case he hl hr)
        (caseWithContext J (fe ≫ J.map (M.coprodIso _ _).hom) fl fr)
  | let₁ (da : Denotes J M ha fa) (db : RegionDenotes hb fb) :
      RegionDenotes (.let₁ ha hb) (bind J fa fb)
  | let₂ (da : Denotes J M ha fa) (db : RegionDenotes hb fb) :
      RegionDenotes (.let₂ ha hb) (bind J fa (
        J.map ((𝟙 _) ⊗ₘ (M.tensorIso _ _).hom) ≫
          J.map (ctxPairIso M _ _ _).hom ≫ fb))
  | cfgZero {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
      {R : Fin 0 → τ} {blocks : Fin 0 → Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
      (de : RegionDenotes he fe) :
      RegionDenotes (.cfg R he hb) fe
  | cfg {n : Nat} {R : Fin n → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : Region Φ} {blocks : Fin n → Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
      {fb : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
        J.obj (labelObj M (List.ofFn R ++ L))}
      {collective : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶
        J.obj (labelObj M (List.ofFn R ++ L))}
      (de : RegionDenotes he fe)
      (db : ∀ i, RegionDenotes (hb i) (fb i))
      (dc : CollectiveDenotes J M Γ R L fb collective) :
      RegionDenotes (.cfg R he hb) (caseWithContext J
        (fe ≫ J.map (labelAppendSplit M (List.ofFn R) L))
        (J.map (CartesianMonoidalCategory.snd _ _))
        (contextualLoop J
          (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelObjToFinite M R) ≫
            collective ≫ J.map (labelAppendSplit M (List.ofFn R) L))))

/-- Transport the graph across proof-irrelevant region typing evidence. -/
theorem RegionDenotes.proof_irrel
    {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    {h h' : Region.HasType Γ r L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M h f) : RegionDenotes J M h' f := by
  rw [Subsingleton.elim h' h]
  exact d

/-- Optional coherence for the relational region semantics. -/
class RegionTypingCoherent : Prop where
  denotes_eq {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
      {h : Region.HasType Γ r L}
      {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} :
      RegionDenotes J M h f → RegionDenotes J M h g → f = g

/-- Every non-recursive region typing derivation, and a zero-block CFG, has a
structural denotation.  The successor CFG case is isolated in
`CollectiveDenotes`: it additionally requires distributing the carried context
over a nonempty finite label coproduct. -/
theorem regionDenotes_exists_nonrecursive
    {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ r L)
    (cfgWitness : ∀ {n : Nat} {R : Fin (n + 1) → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : Region Φ} {blocks : Fin (n + 1) → Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)),
      ∃ f, RegionDenotes J M (.cfg R he hb) f) :
    ∃ f, RegionDenotes J M h f := by
  induction h with
  | br h ha => exact ⟨_, .br (h := h) (denote_spec J M ha)⟩
  | case he hl hr ihl ihr =>
      rcases ihl with ⟨fl, dl⟩
      rcases ihr with ⟨fr, dr⟩
      exact ⟨_, .case (denote_spec J M he) dl dr⟩
  | let₁ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₁ (denote_spec J M ha) db⟩
  | let₂ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₂ (denote_spec J M ha) db⟩
  | @cfg _ _ _ n _ R he hb ihe ihb =>
      cases n with
      | zero =>
          rcases ihe with ⟨fe, de⟩
          exact ⟨fe, .cfgZero he hb de⟩
      | succ n => exact cfgWitness he hb

private theorem regionDenotes_exists
    {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ r L) : ∃ f, RegionDenotes J M h f := by
  induction h with
  | br h ha => exact ⟨_, .br (h := h) (denote_spec J M ha)⟩
  | case he hl hr ihl ihr =>
      rcases ihl with ⟨fl, dl⟩
      rcases ihr with ⟨fr, dr⟩
      exact ⟨_, .case (denote_spec J M he) dl dr⟩
  | let₁ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₁ (denote_spec J M ha) db⟩
  | let₂ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₂ (denote_spec J M ha) db⟩
  | @cfg _ _ _ n _ R he hb ihe ihb =>
      cases n with
      | zero =>
          rcases ihe with ⟨fe, de⟩
          exact ⟨fe, .cfgZero he hb de⟩
      | succ n =>
          rcases ihe with ⟨fe, de⟩
          choose fb db using ihb
          rcases collectiveDenotes_exists_succ J M n _ R _ fb with ⟨fc, dc⟩
          exact ⟨_, .cfg he hb de db dc⟩

/-- Chosen denotation of an exactly typed SSA region. -/
noncomputable def Region.denote {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ r L) :
    J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L) :=
  (regionDenotes_exists J M h).choose

theorem Region.denote_spec {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ r L) :
    RegionDenotes J M h (Region.denote J M h) :=
  (regionDenotes_exists J M h).choose_spec

/-- Under the explicit region-coherence assumption, every structural
denotation is the chosen categorical denotation. -/
theorem RegionDenotes.eq_denote
    [RegionTypingCoherent (Φ := Φ) J M]
    {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    {h : Region.HasType Γ r L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M h f) :
    f = Region.denote J M h :=
  RegionTypingCoherent.denotes_eq d (Region.denote_spec J M h)

end Isotope.LambdaSSA.Semantics.Categorical
