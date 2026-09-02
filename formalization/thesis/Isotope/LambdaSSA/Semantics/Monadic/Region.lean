import Isotope.LambdaSSA.Semantics.Monadic.Term
import Isotope.LambdaSSA.Semantics.Region
import Isotope.LambdaIter.Subtyping.Semantics.Agreement

/-! # Direct monadic semantics of lambda-SSA regions -/

namespace Isotope.LambdaSSA.Semantics.Monadic

set_option autoImplicit true
set_option relaxedAutoImplicit true

open CategoryTheory CategoryTheory.Limits Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

private noncomputable abbrev typeModel :=
  Categorical.ofTypeModel (τ := τ)

/-- The finite dependent sum of values accepted by the labels in `L`.
Using the `Type` coproduct chosen by the categorical infrastructure makes the
comparison map canonical rather than choosing a second encoding of finite sums. -/
noncomputable def LabelDen (L : LCtx τ) : Type v :=
  Categorical.labelObj (typeModel (τ := τ)) L

/-- The same finite label coproduct indexed before materializing `List.ofFn`. -/
noncomputable def FiniteLabelDen {n : Nat} (R : Fin n → τ) : Type v :=
  Categorical.finiteLabelObj (typeModel (τ := τ)) R

noncomputable def finiteLabelInject {n : Nat} (R : Fin n → τ) (i : Fin n) :
    TyDen (R i) → FiniteLabelDen R :=
  Categorical.finiteLabelInject (typeModel (τ := τ)) R i

noncomputable def labelDenToFinite {n : Nat} (R : Fin n → τ) :
    LabelDen (List.ofFn R) → FiniteLabelDen R :=
  Categorical.labelObjToFinite (typeModel (τ := τ)) R

/-- Inject a value into the summand selected by typed label lookup evidence. -/
noncomputable def labelInject {L : LCtx τ} (i : Nat) {A : τ} (h : At L i A) :
    TyDen A → LabelDen L :=
  Categorical.labelInject (typeModel (τ := τ)) i h

/-- Separate external and locally bound destinations of a CFG. -/
noncomputable def labelAppendSplit (R L : LCtx τ) :
    LabelDen (R ++ L) → (LabelDen L ⨿ LabelDen R) :=
  Categorical.labelAppendSplit (typeModel (τ := τ)) R L

/-- A direct collective block function agrees with each constituent block on
the corresponding local-label injection. -/
structure CollectiveDenotes (Γ : VCtx τ) {n : Nat} (R : Fin n → τ) (L : LCtx τ)
    (block : ∀ i, Env (R i :: Γ) → m (LabelDen (List.ofFn R ++ L)))
    (collective : Env Γ × FiniteLabelDen R →
      m (LabelDen (List.ofFn R ++ L))) : Prop where
  restrict (i : Fin n) (ρ : Env Γ) (a : TyDen (R i)) :
    collective (ρ, finiteLabelInject R i a) = block i (ρ, a)

private def envToCategorical : {Γ : VCtx τ} →
    Env Γ → Categorical.ctxObj (typeModel (τ := τ)) Γ
  | [], _ => PUnit.unit
  | _ :: _, ρ => (envToCategorical ρ.1, ρ.2)

private def envFromCategorical : {Γ : VCtx τ} →
    Categorical.ctxObj (typeModel (τ := τ)) Γ → Env Γ
  | [], _ => PUnit.unit
  | _ :: _, ρ => (envFromCategorical ρ.1, ρ.2)

@[simp] private theorem envFrom_to {Γ : VCtx τ} (ρ : Env Γ) :
    envFromCategorical (envToCategorical ρ) = ρ := by
  induction Γ with
  | nil => cases ρ; rfl
  | cons _ _ ih => simp [envFromCategorical, envToCategorical, ih]

/-- Every nonempty finite block family has a collective dispatcher. -/
theorem collectiveDenotes_exists_succ (n : Nat) (Γ : VCtx τ)
    (R : Fin (n + 1) → τ) (L : LCtx τ)
    (block : ∀ i, Env (R i :: Γ) → m (LabelDen (List.ofFn R ++ L))) :
    ∃ collective, CollectiveDenotes Γ R L block collective := by
  let J := CategoryTheory.Kleisli.Adjunction.toKleisli
    (CategoryTheory.ofTypeMonad m)
  let M := Categorical.ofTypeModel (τ := τ)
  let block' : ∀ i, J.obj (Categorical.ctxObj M (R i :: Γ)) ⟶
      J.obj (Categorical.labelObj M (List.ofFn R ++ L)) :=
    fun i => CategoryTheory.Kleisli.Hom.mk (fun ρ => block i (envFromCategorical ρ))
  rcases Categorical.finiteCollective_exists_succ J M n Γ R
      (Categorical.labelObj M (List.ofFn R ++ L)) block' with ⟨f, hf⟩
  refine ⟨fun p => f.of (envToCategorical p.1, p.2), ⟨fun i ρ a => ?_⟩⟩
  have h := congrFun (congrArg CategoryTheory.Kleisli.Hom.of (hf.restrict i))
    (envToCategorical ρ, a)
  simpa [J, M, block', finiteLabelInject, envFromCategorical] using h

/-- Relational graph of the direct monadic region semantics.  Recursive CFGs
feed locally targeted branches back through `iter`; externally targeted
branches are returned. -/
inductive RegionDenotes (ε : Type r) [HasEff Φ ε] [Bot ε]
    [InstructionModel Φ τ ε m] :
    {Γ : VCtx τ} → {region : Region Φ} → {L : LCtx τ} →
    Region.HasType Γ region L → (Env Γ → m (LabelDen L)) → Prop where
  | br (dt : Denotes ε ha fa) :
      RegionDenotes ε (.br h ha) (fun ρ => fa ρ >>= fun a =>
        pure (labelInject _ h a))
  | case {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ}
      {l r : Region Φ}
      {he : Tm.HasType Γ a (LambdaIter.coprod A B)}
      {hl : Region.HasType (A :: Γ) l L}
      {hr : Region.HasType (B :: Γ) r L}
      {fe : Env Γ → m (TyDen (LambdaIter.coprod A B))}
      {fl : Env (A :: Γ) → m (LabelDen L)}
      {fr : Env (B :: Γ) → m (LabelDen L)}
      (de : Denotes ε he fe)
      (dl : RegionDenotes ε hl fl) (dr : RegionDenotes ε hr fr) :
      RegionDenotes ε (.case he hl hr) (fun ρ => fe ρ >>= fun e =>
        match TypeModel.coprodEquiv A B e with
        | .inl a => fl (ρ, a)
        | .inr b => fr (ρ, b))
  | let₁ (da : Denotes ε ha fa) (db : RegionDenotes ε hb fb) :
      RegionDenotes ε (.let₁ ha hb) (fun ρ => fa ρ >>= fun a => fb (ρ, a))
  | let₂ (da : Denotes ε ha fa) (db : RegionDenotes ε hb fb) :
      RegionDenotes ε (.let₂ ha hb) (fun ρ => fa ρ >>= fun ab =>
        let p := TypeModel.tensorEquiv _ _ ab
        fb ((ρ, p.1), p.2))
  | cfgZero {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
      {R : Fin 0 → τ} {blocks : Fin 0 → Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : Env Γ → m (LabelDen L)}
      (de : RegionDenotes ε he fe) :
      RegionDenotes ε (.cfg R he hb) fe
  | cfg {n : Nat} {R : Fin n → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : Region Φ} {blocks : Fin n → Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : Env Γ → m (LabelDen (List.ofFn R ++ L))}
      {fb : ∀ i, Env (R i :: Γ) → m (LabelDen (List.ofFn R ++ L))}
      {collective : Env Γ × FiniteLabelDen R →
        m (LabelDen (List.ofFn R ++ L))}
      (de : RegionDenotes ε he fe)
      (db : ∀ i, RegionDenotes ε (hb i) (fb i))
      (dc : CollectiveDenotes Γ R L fb collective) :
      RegionDenotes ε (.cfg R he hb) (fun ρ => fe ρ >>= fun target =>
        match (Types.binaryCoproductIso (LabelDen L)
          (LabelDen (List.ofFn R))).hom (labelAppendSplit (List.ofFn R) L target) with
        | .inl external => pure external
        | .inr loopTarget => Isotope.Elgot.iter (m := m) (fun current =>
            collective (ρ, labelDenToFinite R current) >>= fun next =>
              pure ((Types.binaryCoproductIso (LabelDen L)
                (LabelDen (List.ofFn R))).hom
                  (labelAppendSplit (List.ofFn R) L next))) loopTarget)

private theorem regionDenotes_exists {Γ : VCtx τ} {region : Region Φ}
    {L : LCtx τ} (h : Region.HasType Γ region L) :
    ∃ f, RegionDenotes (m := m) ε h f := by
  induction h with
  | br h ha => exact ⟨_, .br (h := h) (denote_spec (ε := ε) ha)⟩
  | case he hl hr ihl ihr =>
      rcases ihl with ⟨fl, dl⟩
      rcases ihr with ⟨fr, dr⟩
      exact ⟨_, .case (denote_spec (ε := ε) he) dl dr⟩
  | let₁ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₁ (denote_spec (ε := ε) ha) db⟩
  | let₂ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₂ (denote_spec (ε := ε) ha) db⟩
  | @cfg _ _ _ n _ R he hb ihe ihb =>
      cases n with
      | zero =>
          rcases ihe with ⟨fe, de⟩
          exact ⟨fe, .cfgZero he hb de⟩
      | succ n =>
          rcases ihe with ⟨fe, de⟩
          choose fb db using ihb
          rcases collectiveDenotes_exists_succ n _ R _ fb with ⟨fc, dc⟩
          exact ⟨_, .cfg he hb de db dc⟩

/-- A chosen direct monadic denotation of an exactly typed SSA region. -/
noncomputable def Region.denote {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ region L) : Env Γ → m (LabelDen L) :=
  (regionDenotes_exists (ε := ε) (m := m) h).choose

theorem Region.denote_spec {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ region L) :
    RegionDenotes (m := m) ε h (Region.denote (ε := ε) (m := m) h) :=
  (regionDenotes_exists (ε := ε) (m := m) h).choose_spec

end Isotope.LambdaSSA.Semantics.Monadic
