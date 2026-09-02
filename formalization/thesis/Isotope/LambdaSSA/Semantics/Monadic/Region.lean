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

end Isotope.LambdaSSA.Semantics.Monadic
