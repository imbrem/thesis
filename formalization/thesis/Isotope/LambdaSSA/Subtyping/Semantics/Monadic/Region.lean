import Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Term
import Isotope.LambdaSSA.Semantics.Monadic.Region

/-! # Direct proof-relevant monadic semantics of subtyped SSA regions -/

namespace Isotope.LambdaSSA.Subtyping.Semantics.Monadic

set_option autoImplicit true
set_option relaxedAutoImplicit true

open CategoryTheory CategoryTheory.Limits Isotope.Elgot
open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

abbrev LabelDen {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
    [TypeModel.{u, v} τ] (L : LCtx τ) : Type v :=
  @LambdaSSA.Semantics.Monadic.LabelDen τ _ _ _ L

/-- The collective block graph is representation-independent: subtyping is
carried by each block's proof-relevant term premises, while collective dispatch
only packages their already interpreted functions. -/
abbrev CollectiveDenotes := @LambdaSSA.Semantics.Monadic.CollectiveDenotes

/-- Structural graph of the direct proof-relevant region interpretation.  The
CFG clause records the canonical dependent finite-label dispatcher used by
`denoteRegion`, while its premises expose every block interpretation. -/
inductive RegionDenotes (ε : Type r) [HasEff Φ ε] [Bot ε]
    [InstructionModel Φ τ ε m] :
    {Γ : VCtx τ} → {region : LambdaSSA.Region Φ} → {L : LCtx τ} →
    Region.HasType Γ region L → (Env Γ → m (LabelDen L)) → Prop where
  | br (dt : Denotes ε ha fa) :
      RegionDenotes ε (.br h ha) (fun ρ => fa ρ >>= fun a =>
        pure (LambdaSSA.Semantics.Monadic.labelInject _ h a))
  | case {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : LambdaSSA.Tm Φ}
      {l r : LambdaSSA.Region Φ}
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
  | cfgZero {R : Fin 0 → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : LambdaSSA.Region Φ} {blocks : Fin 0 → LambdaSSA.Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : Env Γ → m (LabelDen L)} (de : RegionDenotes ε he fe) :
      RegionDenotes ε (.cfg R he hb) fe
  | cfg {n : Nat} {R : Fin n → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : LambdaSSA.Region Φ} {blocks : Fin n → LambdaSSA.Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : Env Γ → m (LabelDen (List.ofFn R ++ L))}
      {fb : ∀ i, Env (R i :: Γ) → m (LabelDen (List.ofFn R ++ L))}
      {collective : Env Γ × LambdaSSA.Semantics.Monadic.FiniteLabelDen R →
        m (LabelDen (List.ofFn R ++ L))}
      (de : RegionDenotes ε he fe) (db : ∀ i, RegionDenotes ε (hb i) (fb i))
      (dc : CollectiveDenotes Γ R L fb collective) :
      RegionDenotes ε (.cfg R he hb)
        (fun ρ => fe ρ >>= fun target =>
          match (Types.binaryCoproductIso (LabelDen L) (LabelDen (List.ofFn R))).hom
              (LambdaSSA.Semantics.Monadic.labelAppendSplit (List.ofFn R) L target) with
          | .inl external => pure external
          | .inr loopTarget => Isotope.Elgot.iter (m := m) (fun current =>
              collective (ρ, LambdaSSA.Semantics.Monadic.labelDenToFinite R current) >>=
                fun next => pure ((Types.binaryCoproductIso (LabelDen L)
                  (LabelDen (List.ofFn R))).hom
                    (LambdaSSA.Semantics.Monadic.labelAppendSplit
                      (List.ofFn R) L next))) loopTarget)

private theorem regionDenotes_exists {Γ : VCtx τ} {region : LambdaSSA.Region Φ}
    {L : LCtx τ} (h : Region.HasType Γ region L) :
    ∃ f, RegionDenotes (m := m) ε h f := by
  induction h with
  | br h ha => exact ⟨_, .br (h := h) (denote_spec (ε := ε) ha)⟩
  | case he hl hr ihl ihr =>
      rcases ihl with ⟨fl, dl⟩; rcases ihr with ⟨fr, dr⟩
      exact ⟨_, .case (denote_spec (ε := ε) he) dl dr⟩
  | let₁ ha hb ih => rcases ih with ⟨fb, db⟩; exact ⟨_, .let₁ (denote_spec (ε := ε) ha) db⟩
  | let₂ ha hb ih => rcases ih with ⟨fb, db⟩; exact ⟨_, .let₂ (denote_spec (ε := ε) ha) db⟩
  | @cfg _ _ _ n _ R he hb ihe ihb =>
      cases n with
      | zero => rcases ihe with ⟨fe, de⟩; exact ⟨fe, .cfgZero he hb de⟩
      | succ n =>
          rcases ihe with ⟨fe, de⟩
          choose fb db using ihb
          rcases LambdaSSA.Semantics.Monadic.collectiveDenotes_exists_succ
            n _ R _ fb with ⟨fc, dc⟩
          exact ⟨_, .cfg he hb de db dc⟩

noncomputable def denoteRegion {Γ : VCtx τ} {region : LambdaSSA.Region Φ}
    {L : LCtx τ} (h : Region.HasType Γ region L) : Env Γ → m (LabelDen L) :=
  (regionDenotes_exists (ε := ε) (m := m) h).choose

theorem denoteRegion_spec {Γ : VCtx τ} {region : LambdaSSA.Region Φ}
    {L : LCtx τ} (h : Region.HasType Γ region L) :
    RegionDenotes ε h (denoteRegion (ε := ε) (m := m) h) :=
  (regionDenotes_exists (ε := ε) (m := m) h).choose_spec

end Isotope.LambdaSSA.Subtyping.Semantics.Monadic
