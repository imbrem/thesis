import Isotope.LambdaSSA.Semantics.Monadic.Region

/-! # Optional coherence of direct monadic region semantics -/

namespace Isotope.LambdaSSA.Semantics.Monadic

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]

/-- Transport the monadic denotation graph across proof-irrelevant evidence
for the same exact region typing judgment. -/
theorem RegionDenotes.proof_irrel
    {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    {h h' : Region.HasType Γ region L}
    {f : Env Γ → m (LabelDen L)}
    (d : RegionDenotes (m := m) ε h f) : RegionDenotes (m := m) ε h' f := by
  rw [Subsingleton.elim h' h]
  exact d

/-- Explicit semantic proof-irrelevance assumption for regions.  It is not
derivable from the present raw typing relation: type formers and instruction
typing are intentionally proof-relevant and need not be injective. -/
class RegionTypingCoherent : Prop where
  denotes_eq {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
      {h : Region.HasType Γ region L}
      {f g : Env Γ → m (LabelDen L)} :
    RegionDenotes (m := m) ε h f → RegionDenotes (m := m) ε h g → f = g

/-- Under explicit coherence, every relational denotation agrees with the
chosen direct denotation. -/
theorem RegionDenotes.eq_denote
    [RegionTypingCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)]
    {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    {h : Region.HasType Γ region L} {f : Env Γ → m (LabelDen L)}
    (d : RegionDenotes (m := m) ε h f) :
    f = Region.denote (ε := ε) (m := m) h :=
  RegionTypingCoherent.denotes_eq d (Region.denote_spec (ε := ε) (m := m) h)

end Isotope.LambdaSSA.Semantics.Monadic
