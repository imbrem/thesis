import Isotope.LambdaSSA.Semantics.Finite
import Isotope.LambdaSSA.Semantics.Region
import Isotope.LambdaIter.Subtyping.Semantics.Agreement
import Isotope.LambdaSSA.Semantics.Monadic.Model

/-! # Canonical values for lambda-SSA label contexts

This recursive sum representation exposes label routing computationally.  It
is kept separate from the categorical finite coproduct used by the abstract
semantics; an explicit comparison equivalence can mediate between them.
-/

namespace Isotope.LambdaSSA.Semantics.Monadic

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open CategoryTheory CategoryTheory.Limits

universe u v

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]

private noncomputable abbrev categoricalTypeModel :=
  Categorical.ofTypeModel (τ := τ)

private theorem eqToHom_cast_cancel {X Y : Type v}
    (h : X = Y) (h' : Y = X) (x : X) :
    (eqToHom h' : Y ⟶ X) (h ▸ x) = x := by
  subst Y
  rfl

private theorem categorical_eqToHom_apply {A B : τ} (h : A = B)
    (a : TyDen A) :
    (eqToHom (congrArg (categoricalTypeModel (τ := τ)).obj h) :
      TyDen A ⟶ TyDen B) a = h ▸ a := by
  subst B
  rfl

/-- The label coproduct used by the original categorical presentation. -/
noncomputable abbrev CategoricalLabelDen (L : LCtx τ) : Type v :=
  Isotope.LambdaSSA.Semantics.Categorical.labelObj
    (categoricalTypeModel (τ := τ)) L

/-- The chosen categorical coproduct in `Type` is canonically equivalent to
the ordinary dependent sum over its injections.  Keeping the family in one
definition avoids any coherence claim between separately chosen colimits. -/
noncomputable def categoricalSigmaEquiv (L : LCtx τ) :
    (Σ i : Fin L.length, TyDen (L.get i)) ≃ CategoricalLabelDen L := by
  let F : Fin L.length → Type v := fun i => TyDen (L.get i)
  let c : Cofan F := Cofan.mk (f := F) (∐ F) (Limits.Sigma.ι F)
  exact CofanTypes.equivOfIsColimit
    ((Cofan.isColimit_cofanTypes_iff c).2 ⟨Limits.coproductIsCoproduct F⟩)

@[simp] theorem categoricalSigmaEquiv_apply (L : LCtx τ)
    (i : Fin L.length) (a : TyDen (L.get i)) :
    categoricalSigmaEquiv L ⟨i, a⟩ =
      Limits.Sigma.ι (fun j : Fin L.length => TyDen (L.get j)) i a := by
  unfold categoricalSigmaEquiv
  apply CofanTypes.equivOfIsColimit_apply

/-- A value targeted at one label of a newest-first label context. -/
def LabelValue : LCtx τ → Type v
  | [] => PEmpty
  | A :: L => TyDen A ⊕ LabelValue L

def LabelValue.toSigma : (L : LCtx τ) → LabelValue L →
    Σ i : Fin L.length, TyDen (L.get i)
  | [], x => nomatch x
  | _ :: _, Sum.inl a => ⟨0, a⟩
  | _ :: L, Sum.inr x =>
      let ⟨i, a⟩ := LabelValue.toSigma L x
      ⟨i.succ, a⟩

def LabelValue.fromSigma : (L : LCtx τ) →
    (Σ i : Fin L.length, TyDen (L.get i)) → LabelValue L
  | [], x => Fin.elim0 x.1
  | _ :: L, ⟨i, a⟩ => Fin.cases Sum.inl
      (fun j a => Sum.inr (LabelValue.fromSigma L ⟨j, a⟩)) i a

theorem LabelValue.fromSigma_toSigma : (L : LCtx τ) → (x : LabelValue L) →
    LabelValue.fromSigma L (LabelValue.toSigma L x) = x
  | [], x => nomatch x
  | _ :: _, Sum.inl _ => rfl
  | _ :: L, Sum.inr x => by
      simp only [LabelValue.toSigma, LabelValue.fromSigma, Fin.cases_succ]
      exact congrArg Sum.inr (LabelValue.fromSigma_toSigma L x)

theorem LabelValue.toSigma_fromSigma : (L : LCtx τ) →
    (x : Σ i : Fin L.length, TyDen (L.get i)) →
      LabelValue.toSigma L (LabelValue.fromSigma L x) = x
  | [], x => Fin.elim0 x.1
  | A :: L, ⟨i, a⟩ => by
      refine Fin.cases (motive := fun i => ∀ a : TyDen ((A :: L).get i),
        LabelValue.toSigma (A :: L)
          (LabelValue.fromSigma (A :: L) ⟨i, a⟩) = ⟨i, a⟩)
        ?_ (fun j => ?_) i a
      · intro a
        rfl
      · intro a
        have ih := LabelValue.toSigma_fromSigma L ⟨j, a⟩
        simp only [LabelValue.fromSigma, LabelValue.toSigma, Fin.cases_succ]
        rw [ih]

def LabelValue.sigmaEquiv (L : LCtx τ) :
    LabelValue L ≃ (Σ i : Fin L.length, TyDen (L.get i)) where
  toFun := LabelValue.toSigma L
  invFun := LabelValue.fromSigma L
  left_inv := LabelValue.fromSigma_toSigma L
  right_inv := LabelValue.toSigma_fromSigma L

/-- Canonical comparison with the categorical label coproduct. -/
noncomputable def LabelValue.categoricalEquiv (L : LCtx τ) :
    LabelValue L ≃ CategoricalLabelDen L :=
  (LabelValue.sigmaEquiv L).trans (categoricalSigmaEquiv L)

theorem LabelValue.categoricalEquiv_apply (L : LCtx τ) (x : LabelValue L) :
    LabelValue.categoricalEquiv L x =
      Limits.Sigma.ι (fun i : Fin L.length => TyDen (L.get i))
        (LabelValue.toSigma L x).1 (LabelValue.toSigma L x).2 := by
  unfold LabelValue.categoricalEquiv LabelValue.sigmaEquiv
  apply categoricalSigmaEquiv_apply

/-- Type-level application form of the categorical append-split injection
equation.  This removes the categorical-composition coercion at call sites. -/
theorem labelAppendSplit_ι_apply (R L : LCtx τ)
    (i : Fin (R ++ L).length) (a : TyDen ((R ++ L).get i)) :
    Isotope.LambdaSSA.Semantics.Categorical.labelAppendSplit
        (categoricalTypeModel (τ := τ)) R L
        (Limits.Sigma.ι (fun k : Fin (R ++ L).length =>
          TyDen ((R ++ L).get k)) i a) =
      Isotope.LambdaSSA.Semantics.Categorical.labelAppendRoute
        (categoricalTypeModel (τ := τ)) R L i a := by
  exact congrFun
    (Isotope.LambdaSSA.Semantics.Categorical.labelAppendSplit_ι
      (categoricalTypeModel (τ := τ)) R L i) a

/-- Compare the recursive representation with the categorical coproduct,
without identifying independently chosen coproduct presentations. -/
noncomputable def LabelValue.toCategorical : (L : LCtx τ) →
    LabelValue L → CategoricalLabelDen L
  | [], x => nomatch x
  | A :: L, Sum.inl a =>
      Isotope.LambdaSSA.Semantics.Categorical.labelConsFrom
        (categoricalTypeModel (τ := τ)) A L
        ((coprod.inl : TyDen A ⟶ TyDen A ⨿ CategoricalLabelDen L) a)
  | A :: L, Sum.inr x =>
      Isotope.LambdaSSA.Semantics.Categorical.labelConsFrom
        (categoricalTypeModel (τ := τ)) A L
        ((coprod.inr : CategoricalLabelDen L ⟶
          TyDen A ⨿ CategoricalLabelDen L) (LabelValue.toCategorical L x))

/-- Decode the categorical coproduct into the recursive representation. -/
noncomputable def LabelValue.fromCategorical : (L : LCtx τ) →
    CategoricalLabelDen L → LabelValue L
  | [], x => by
      let F := Discrete.functor
        (fun i : Fin 0 => (categoricalTypeModel (τ := τ)).obj ([].get i))
      let q := (Types.colimitEquivColimitType F) x
      exact Fin.elim0 q.out.1.as
  | A :: L, x =>
      match (Types.binaryCoproductIso (TyDen A) (CategoricalLabelDen L)).hom
        (Isotope.LambdaSSA.Semantics.Categorical.labelConsTo
          (categoricalTypeModel (τ := τ)) A L x) with
      | Sum.inl a => Sum.inl a
      | Sum.inr y => Sum.inr (LabelValue.fromCategorical L y)

theorem LabelValue.fromCategorical_toCategorical :
    (L : LCtx τ) → (x : LabelValue L) →
      LabelValue.fromCategorical L (LabelValue.toCategorical L x) = x
  | [], x => nomatch x
  | A :: L, Sum.inl a => by
      have hc : Isotope.LambdaSSA.Semantics.Categorical.labelConsTo
          (categoricalTypeModel (τ := τ)) A L
          (Isotope.LambdaSSA.Semantics.Categorical.labelConsFrom
            (categoricalTypeModel (τ := τ)) A L
            ((coprod.inl : TyDen A ⟶ TyDen A ⨿ CategoricalLabelDen L) a)) =
          (coprod.inl : TyDen A ⟶ TyDen A ⨿ CategoricalLabelDen L) a := by
        calc
          _ = Isotope.LambdaSSA.Semantics.Categorical.labelConsTo
              (categoricalTypeModel (τ := τ)) A L
              (Limits.Sigma.ι (fun k : Fin (A::L).length =>
                (categoricalTypeModel (τ := τ)).obj ((A::L).get k)) 0 a) :=
            congrArg _ (congrFun
              (Isotope.LambdaSSA.Semantics.Categorical.labelConsFrom_head
                (categoricalTypeModel (τ := τ)) A L) a)
          _ = _ := congrFun
            (Isotope.LambdaSSA.Semantics.Categorical.labelConsTo_head
              (categoricalTypeModel (τ := τ)) A L) a
      simp only [LabelValue.toCategorical, LabelValue.fromCategorical, hc]
      have hb := congrFun (Types.binaryCoproductIso_inl_comp_hom
        (TyDen A) (CategoricalLabelDen L)) a
      exact congrArg (fun z => match z with
        | Sum.inl b => Sum.inl b
        | Sum.inr z => Sum.inr (LabelValue.fromCategorical L z)) hb
  | A :: L, Sum.inr x => by
      let y := LabelValue.toCategorical L x
      have hc : Isotope.LambdaSSA.Semantics.Categorical.labelConsTo
          (categoricalTypeModel (τ := τ)) A L
          (Isotope.LambdaSSA.Semantics.Categorical.labelConsFrom
            (categoricalTypeModel (τ := τ)) A L
            ((coprod.inr : CategoricalLabelDen L ⟶
              TyDen A ⨿ CategoricalLabelDen L) y)) =
          (coprod.inr : CategoricalLabelDen L ⟶
            TyDen A ⨿ CategoricalLabelDen L) y := by
        obtain ⟨i, a, hi⟩ := Types.jointly_surjective' y
        rw [← hi]
        rcases i with ⟨i⟩
        calc
          _ = Isotope.LambdaSSA.Semantics.Categorical.labelConsTo
              (categoricalTypeModel (τ := τ)) A L
              (Limits.Sigma.ι (fun k : Fin (A::L).length =>
                (categoricalTypeModel (τ := τ)).obj ((A::L).get k)) i.succ a) :=
            congrArg _ (congrFun
              (Isotope.LambdaSSA.Semantics.Categorical.labelConsFrom_tail
                (categoricalTypeModel (τ := τ)) A L i) a)
          _ = _ := congrFun
            (Isotope.LambdaSSA.Semantics.Categorical.labelConsTo_tail
              (categoricalTypeModel (τ := τ)) A L i) a
      simp only [LabelValue.toCategorical, LabelValue.fromCategorical]
      rw [hc]
      have hb := congrFun (Types.binaryCoproductIso_inr_comp_hom
        (TyDen A) (CategoricalLabelDen L)) y
      have hb' : (Types.binaryCoproductIso
          (TyDen A) (CategoricalLabelDen L)).hom
          ((coprod.inr : CategoricalLabelDen L ⟶
            TyDen A ⨿ CategoricalLabelDen L) y) = Sum.inr y := hb
      rw [hb']
      exact congrArg Sum.inr (LabelValue.fromCategorical_toCategorical L x)

/-- Inject a value using typed label lookup evidence. -/
def LabelValue.inject : {L : LCtx τ} → (i : Nat) → {A : τ} →
    At L i A → TyDen A → LabelValue L
  | [], _, _, h, _ => by simp [At] at h
  | B :: _, 0, A, h, a => by
      have e : B = A := by simpa [At] using h
      exact Sum.inl (e ▸ a)
  | _ :: L, i + 1, _, h, a => Sum.inr (LabelValue.inject (L := L) i h a)

/-- The dependent-sum value selected by typed label lookup evidence. -/
def LabelValue.sigmaInject {L : LCtx τ} (i : Nat) {A : τ}
    (h : At L i A) (a : TyDen A) : Σ j : Fin L.length, TyDen (L.get j) :=
  let hi : i < L.length := (List.getElem?_eq_some_iff.mp h).1
  let j : Fin L.length := ⟨i, hi⟩
  let hj : L.get j = A := (List.getElem?_eq_some_iff.mp h).2
  ⟨j, hj.symm ▸ a⟩

/-- Recursive injection exposes exactly the lookup-selected dependent-sum
index and its explicitly transported payload. -/
theorem LabelValue.toSigma_inject : {L : LCtx τ} → (i : Nat) → {A : τ} →
    (h : At L i A) → (a : TyDen A) →
    LabelValue.toSigma L (LabelValue.inject i h a) =
      LabelValue.sigmaInject i h a
  | [], _, _, h, _ => by simp [At] at h
  | B :: L, 0, A, h, a => by
      simp [LabelValue.inject, LabelValue.toSigma, LabelValue.sigmaInject, At]
      rfl
  | B :: L, i + 1, A, h, a => by
      simp only [LabelValue.inject, LabelValue.toSigma]
      rw [LabelValue.toSigma_inject i h a]
      simp [LabelValue.sigmaInject]

@[simp] theorem LabelValue.categoricalEquiv_inject {L : LCtx τ} (i : Nat)
    {A : τ} (h : At L i A) (a : TyDen A) :
    LabelValue.categoricalEquiv L (LabelValue.inject i h a) =
      Isotope.LambdaSSA.Semantics.Categorical.labelInject
        (categoricalTypeModel (τ := τ)) i h a := by
  rw [LabelValue.categoricalEquiv_apply, LabelValue.toSigma_inject]
  rw [Isotope.LambdaSSA.Semantics.Categorical.labelInject_eq_sigma]
  dsimp [LabelValue.sigmaInject]
  apply congrArg (fun z : TyDen (L.get ⟨i,
      (List.getElem?_eq_some_iff.mp h).1⟩) =>
    Limits.Sigma.ι (fun k : Fin L.length => TyDen (L.get k)) ⟨i,
      (List.getElem?_eq_some_iff.mp h).1⟩ z)
  exact (categorical_eqToHom_apply
    (List.getElem?_eq_some_iff.mp h).2.symm a).symm

@[simp] theorem LabelValue.inject_succ {B A : τ} {L : LCtx τ} (i : Nat)
    (h : At (B :: L) (i + 1) A) (ht : At L i A) (a : TyDen A) :
    LabelValue.inject (i + 1) h a = Sum.inr (LabelValue.inject i ht a) := by
  rfl

/-- Separate external and locally bound destinations without categorical
casts.  Local labels occupy the left prefix of the appended context. -/
def LabelValue.appendSplit : (R L : LCtx τ) →
    LabelValue (R ++ L) → LabelValue L ⊕ LabelValue R
  | [], _, x => Sum.inl x
  | _ :: R, L, Sum.inl a => Sum.inr (Sum.inl a)
  | _ :: R, L, Sum.inr x =>
      match LabelValue.appendSplit R L x with
      | Sum.inl external => Sum.inl external
      | Sum.inr inside => Sum.inr (Sum.inr inside)

/-- `appendSplit` computes the expected arithmetic decomposition of the
index exposed by `toSigma`: local indices are unchanged, while external
indices are shifted past the local prefix. -/
theorem LabelValue.appendSplit_toSigma_index :
    (R L : LCtx τ) → (x : LabelValue (R ++ L)) →
    match LabelValue.appendSplit R L x with
    | Sum.inl external =>
        (LabelValue.toSigma (R ++ L) x).1.val =
          R.length + (LabelValue.toSigma L external).1.val
    | Sum.inr inside =>
        (LabelValue.toSigma (R ++ L) x).1.val =
          (LabelValue.toSigma R inside).1.val
  | [], _, _ => by simp [LabelValue.appendSplit]
  | _ :: _, _, Sum.inl _ => rfl
  | A :: R, L, Sum.inr x => by
      have ih := LabelValue.appendSplit_toSigma_index R L x
      generalize hs : LabelValue.appendSplit R L x = s at ih ⊢
      cases s <;> simp [LabelValue.appendSplit, LabelValue.toSigma, hs] at ih ⊢ <;>
        omega

def LabelValue.sigmaLocal (R L : LCtx τ) :
    (Σ i : Fin R.length, TyDen (R.get i)) →
      (Σ i : Fin (R ++ L).length, TyDen ((R ++ L).get i))
  | ⟨i, a⟩ => ⟨Fin.castLE (by simp) i, by simpa using a⟩

def LabelValue.sigmaExternal (R L : LCtx τ) :
    (Σ i : Fin L.length, TyDen (L.get i)) →
      (Σ i : Fin (R ++ L).length, TyDen ((R ++ L).get i))
  | ⟨i, a⟩ => ⟨Fin.cast List.length_append.symm (Fin.natAdd R.length i),
      by simpa using a⟩

/-- Payload-preserving version of `appendSplit_toSigma_index`. -/
theorem LabelValue.appendSplit_toSigma :
    (R L : LCtx τ) → (x : LabelValue (R ++ L)) →
    match LabelValue.appendSplit R L x with
    | Sum.inl external => LabelValue.toSigma (R ++ L) x =
        LabelValue.sigmaExternal R L (LabelValue.toSigma L external)
    | Sum.inr inside => LabelValue.toSigma (R ++ L) x =
        LabelValue.sigmaLocal R L (LabelValue.toSigma R inside)
  | [], L, x => by
      rcases h : LabelValue.toSigma L x with ⟨i, a⟩
      simp [LabelValue.appendSplit, LabelValue.sigmaExternal, h]
      exact (Sigma.ext_iff.mp h).2.symm
  | _ :: _, _, Sum.inl _ => rfl
  | A :: R, L, Sum.inr x => by
      have ih := LabelValue.appendSplit_toSigma R L x
      generalize hs : LabelValue.appendSplit R L x = s at ih ⊢
      cases s <;> simp [LabelValue.appendSplit, LabelValue.toSigma,
        LabelValue.sigmaLocal, LabelValue.sigmaExternal, hs] at ⊢
      · rw [ih]
        constructor
        · apply Fin.ext; simp [LabelValue.sigmaExternal]; omega
        · simp [LabelValue.sigmaExternal]
      · rw [ih]
        constructor
        · apply Fin.ext; simp [LabelValue.sigmaLocal]
        · simp [LabelValue.sigmaLocal]

/-- The recursive append splitter agrees pointwise with the categorical
coproduct splitter under the canonical label equivalences. -/
theorem LabelValue.categoricalEquiv_appendSplit (R L : LCtx τ)
    (x : LabelValue (R ++ L)) :
    Isotope.LambdaSSA.Semantics.Categorical.labelAppendSplit
        (categoricalTypeModel (τ := τ)) R L
        (LabelValue.categoricalEquiv (R ++ L) x) =
      match LabelValue.appendSplit R L x with
      | Sum.inl external =>
          (coprod.inl : CategoricalLabelDen L ⟶
            CategoricalLabelDen L ⨿ CategoricalLabelDen R)
            (LabelValue.categoricalEquiv L external)
      | Sum.inr inside =>
          (coprod.inr : CategoricalLabelDen R ⟶
            CategoricalLabelDen L ⨿ CategoricalLabelDen R)
            (LabelValue.categoricalEquiv R inside) := by
  rw [LabelValue.categoricalEquiv_apply, labelAppendSplit_ι_apply]
  have hp := LabelValue.appendSplit_toSigma R L x
  generalize hs : LabelValue.appendSplit R L x = s at hp ⊢
  cases s with
  | inl external =>
      simp only at hp ⊢
      rcases ht : LabelValue.toSigma L external with ⟨i, a⟩
      simp only [ht] at hp ⊢
      rw [hp]
      unfold Isotope.LambdaSSA.Semantics.Categorical.labelAppendRoute
      simp [LabelValue.sigmaExternal, LabelValue.categoricalEquiv_apply]
      rw [Isotope.LambdaSSA.Semantics.Categorical.labelInject_eq_sigma]
      rw [ht]
      apply congrArg (fun z : TyDen (L.get i) =>
        (coprod.inl : CategoricalLabelDen L ⟶
          CategoricalLabelDen L ⨿ CategoricalLabelDen R)
          (Limits.Sigma.ι (fun k : Fin L.length => TyDen (L.get k)) i z))
      apply eqToHom_cast_cancel
  | inr inside =>
      simp only at hp ⊢
      rcases ht : LabelValue.toSigma R inside with ⟨i, a⟩
      simp only [ht] at hp ⊢
      rw [hp]
      unfold Isotope.LambdaSSA.Semantics.Categorical.labelAppendRoute
      simp [LabelValue.sigmaLocal, LabelValue.categoricalEquiv_apply]
      rw [Isotope.LambdaSSA.Semantics.Categorical.labelInject_eq_sigma]
      rw [ht]
      apply congrArg (fun z : TyDen (R.get i) =>
        (coprod.inr : CategoricalLabelDen R ⟶
          CategoricalLabelDen L ⨿ CategoricalLabelDen R)
          (Limits.Sigma.ι (fun k : Fin R.length => TyDen (R.get k)) i z))
      apply eqToHom_cast_cancel


@[simp] theorem LabelValue.appendSplit_inject_local :
    {R L : LCtx τ} → (i : Nat) → {A : τ} →
    (hR : At R i A) → (hRL : At (R ++ L) i A) → (a : TyDen A) →
    LabelValue.appendSplit R L (LabelValue.inject i hRL a) =
      Sum.inr (LabelValue.inject i hR a)
  | [], _, _, _, h, _, _ => by simp [At] at h
  | _ :: _, _, 0, _, _, _, _ => rfl
  | B :: R, L, i + 1, A, hR, hRL, a => by
      have htR : At R i A := by simpa [At] using hR
      have htRL : At (R ++ L) i A := by simpa [At] using hRL
      change LabelValue.appendSplit (B :: R) L
        (Sum.inr (LabelValue.inject i htRL a)) =
        Sum.inr (Sum.inr (LabelValue.inject i htR a))
      simp only [LabelValue.appendSplit]
      rw [LabelValue.appendSplit_inject_local i htR htRL a]
      rfl

@[simp] theorem LabelValue.appendSplit_inject_external :
    (R L : LCtx τ) → (i : Nat) → {A : τ} →
    (hL : At L i A) → (hRL : At (R ++ L) (i + R.length) A) → (a : TyDen A) →
    LabelValue.appendSplit R L (LabelValue.inject (i + R.length) hRL a) =
      Sum.inl (LabelValue.inject i hL a)
  | [], _, _, _, _, _, _ => rfl
  | B :: R, L, i, A, hL, hRL, a => by
      have htRL : At (R ++ L) (i + R.length) A := by
        simpa [At] using hRL
      change LabelValue.appendSplit (B :: R) L
        (Sum.inr (LabelValue.inject (i + R.length) htRL a)) =
        Sum.inl (LabelValue.inject i hL a)
      simp only [LabelValue.appendSplit]
      rw [LabelValue.appendSplit_inject_external R L i hL htRL a]

/-- The sole label of a one-element `Fin` family routes to the local side. -/
@[simp] theorem LabelValue.appendSplit_ofFn_one_inject_zero
    (L : LCtx τ) (X : τ)
    (h : At (List.ofFn (fun _ : Fin 1 => X) ++ L) 0 X) (a : TyDen X) :
    LabelValue.appendSplit (List.ofFn (fun _ : Fin 1 => X)) L
        (LabelValue.inject 0 h a) = Sum.inr (Sum.inl a) := by
  have hof : List.ofFn (fun _ : Fin 1 => X) = [X] := by simp
  cases hof
  rfl

/-- A destination after the sole local label of a one-element family routes
to the corresponding external destination. -/
@[simp] theorem LabelValue.appendSplit_ofFn_one_inject_external
    (L : LCtx τ) (X : τ) (i : Nat) {A : τ}
    (hL : At L i A)
    (hRL : At (List.ofFn (fun _ : Fin 1 => X) ++ L) (i + 1) A)
    (a : TyDen A) :
    LabelValue.appendSplit (List.ofFn (fun _ : Fin 1 => X)) L
        (LabelValue.inject (i + 1) hRL a) =
      Sum.inl (LabelValue.inject i hL a) := by
  have hof : List.ofFn (fun _ : Fin 1 => X) = [X] := by simp
  cases hof
  simpa using LabelValue.appendSplit_inject_external [X] L i hL hRL a

end Isotope.LambdaSSA.Semantics.Monadic
