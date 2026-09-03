import Isotope.LambdaSSA.Semantics.Monadic.Term
import Isotope.LambdaSSA.Semantics.Monadic.Label
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
def LabelDen (L : LCtx τ) : Type v := LabelValue L

/-- A directly inspectable finite label destination. -/
def FiniteLabelDen {n : Nat} (R : Fin n → τ) : Type v :=
  Σ i : Fin n, TyDen (R i)

def finiteLabelInject {n : Nat} (R : Fin n → τ) (i : Fin n) :
    TyDen (R i) → FiniteLabelDen R :=
  fun a => ⟨i, a⟩

theorem finiteLabelDen_exists {n : Nat} (R : Fin n → τ)
    (x : FiniteLabelDen R) :
    ∃ (i : Fin n) (a : TyDen (R i)), finiteLabelInject R i a = x := by
  exact ⟨x.1, x.2, rfl⟩

noncomputable def finiteCategoricalEquiv {n : Nat} (R : Fin n → τ) :
    FiniteLabelDen R ≃ Categorical.finiteLabelObj (typeModel (τ := τ)) R := by
  let c : Cofan (fun i => TyDen (R i)) := Cofan.mk (f := fun i => TyDen (R i))
    (∐ fun i => TyDen (R i)) (Limits.Sigma.ι fun i => TyDen (R i))
  exact CofanTypes.equivOfIsColimit
    ((Cofan.isColimit_cofanTypes_iff c).2
      ⟨Limits.coproductIsCoproduct (fun i => TyDen (R i))⟩)

theorem finiteLabelDen_funext {n : Nat} (R : Fin n → τ) {X : Sort*}
    {f g : FiniteLabelDen R → X}
    (h : ∀ i a, f (finiteLabelInject R i a) =
      g (finiteLabelInject R i a)) : f = g := by
  funext x
  obtain ⟨i, a, rfl⟩ := finiteLabelDen_exists R x
  exact h i a

noncomputable def labelDenToFinite {n : Nat} (R : Fin n → τ) :
    LabelDen (List.ofFn R) → FiniteLabelDen R :=
  (finiteCategoricalEquiv R).symm ∘
    Categorical.labelObjToFinite (typeModel (τ := τ)) R ∘
    LabelValue.categoricalEquiv (List.ofFn R)

/-- Inject a value into the summand selected by typed label lookup evidence. -/
noncomputable def labelInject {L : LCtx τ} (i : Nat) {A : τ} (h : At L i A) :
    TyDen A → LabelDen L :=
  fun a => (LabelValue.categoricalEquiv L).symm
    (Categorical.labelInject (typeModel (τ := τ)) i h a)

@[simp] theorem categoricalEquiv_labelInject {L : LCtx τ} (i : Nat)
    {A : τ} (h : At L i A) (a : TyDen A) :
    LabelValue.categoricalEquiv L (labelInject i h a) =
      Categorical.labelInject (typeModel (τ := τ)) i h a := by
  exact Equiv.apply_symm_apply _ _

/-- The original categorical definition of monadic label injection computes
to the canonical recursive label value. -/
@[simp] theorem labelInject_eq_recursive {L : LCtx τ} (i : Nat)
    {A : τ} (h : At L i A) (a : TyDen A) :
    labelInject i h a = LabelValue.inject i h a := by
  apply (LabelValue.categoricalEquiv L).injective
  rw [categoricalEquiv_labelInject, LabelValue.categoricalEquiv_inject]

/-- Separate external and locally bound destinations of a CFG. -/
noncomputable def labelAppendSplit (R L : LCtx τ) :
    LabelDen (R ++ L) → (LabelDen L ⨿ LabelDen R) :=
  (Types.binaryCoproductIso (LabelDen L) (LabelDen R)).inv ∘
    LabelValue.appendSplit R L

@[simp] theorem binaryCoproductIso_hom_labelAppendSplit
    (R L : LCtx τ) (x : LabelDen (R ++ L)) :
    (Types.binaryCoproductIso (LabelDen L) (LabelDen R)).hom
        (labelAppendSplit R L x) = LabelValue.appendSplit R L x := by
  unfold labelAppendSplit
  exact (Types.binaryCoproductIso (LabelDen L) (LabelDen R)).inv_hom_id_apply _

theorem labelDenToFinite_inject {n : Nat} (R : Fin n → τ) (i : Fin n)
    (h : At (List.ofFn R) i.val (R i)) (a : TyDen (R i)) :
    labelDenToFinite R (labelInject i.val h a) = finiteLabelInject R i a := by
  have hc := congrFun (Categorical.labelInject_labelObjToFinite
    (typeModel (τ := τ)) R i h) a
  unfold labelDenToFinite labelInject finiteLabelInject
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  change (finiteCategoricalEquiv R).symm
    (Categorical.labelObjToFinite (typeModel (τ := τ)) R
      (Categorical.labelInject (typeModel (τ := τ)) i.val h a)) = ⟨i, a⟩
  have hc' : Categorical.labelObjToFinite (typeModel (τ := τ)) R
      (Categorical.labelInject (typeModel (τ := τ)) i.val h a) =
      Categorical.finiteLabelInject (typeModel (τ := τ)) R i a := hc
  rw [hc']
  unfold finiteCategoricalEquiv Categorical.finiteLabelInject
  apply CofanTypes.equivOfIsColimit_symm_apply

@[simp] theorem labelDenToFinite_recursiveInject {n : Nat} (R : Fin n → τ)
    (i : Fin n) (h : At (List.ofFn R) i.val (R i)) (a : TyDen (R i)) :
    labelDenToFinite R (LabelValue.inject i.val h a) = finiteLabelInject R i a := by
  rw [← labelInject_eq_recursive]
  exact labelDenToFinite_inject R i h a

/-- A direct collective block function agrees with each constituent block on
the corresponding local-label injection. -/
structure CollectiveDenotes (Γ : VCtx τ) {n : Nat} (R : Fin n → τ) (L : LCtx τ)
    (block : ∀ i, Env (R i :: Γ) → m (LabelDen (List.ofFn R ++ L)))
    (collective : Env Γ × FiniteLabelDen R →
      m (LabelDen (List.ofFn R ++ L))) : Prop where
  restrict (i : Fin n) (ρ : Env Γ) (a : TyDen (R i)) :
    collective (ρ, finiteLabelInject R i a) = block i (ρ, a)

theorem CollectiveDenotes.dispatch
    {Γ : VCtx τ} {n : Nat} {R : Fin n → τ} {L : LCtx τ}
    {block : ∀ i, Env (R i :: Γ) → m (LabelDen (List.ofFn R ++ L))}
    {collective : Env Γ × FiniteLabelDen R →
      m (LabelDen (List.ofFn R ++ L))}
    (h : CollectiveDenotes Γ R L block collective)
    (ρ : Env Γ) (x : FiniteLabelDen R) :
    ∃ (i : Fin n) (a : TyDen (R i)),
      x = finiteLabelInject R i a ∧ collective (ρ, x) = block i (ρ, a) := by
  obtain ⟨i, a, ha⟩ := finiteLabelDen_exists R x
  subst x
  exact ⟨i, a, rfl, h.restrict i ρ a⟩

theorem CollectiveDenotes.eq
    {Γ : VCtx τ} {n : Nat} {R : Fin n → τ} {L : LCtx τ}
    {block : ∀ i, Env (R i :: Γ) → m (LabelDen (List.ofFn R ++ L))}
    {f g : Env Γ × FiniteLabelDen R →
      m (LabelDen (List.ofFn R ++ L))}
    (hf : CollectiveDenotes Γ R L block f)
    (hg : CollectiveDenotes Γ R L block g) : f = g := by
  funext p
  obtain ⟨ρ, x⟩ := p
  obtain ⟨i, a, rfl⟩ := finiteLabelDen_exists R x
  exact (hf.restrict i ρ a).trans (hg.restrict i ρ a).symm

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
  refine ⟨fun p => block p.2.1 (p.1, p.2.2), ⟨fun i ρ a => ?_⟩⟩
  rfl

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
