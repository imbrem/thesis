import Isotope.LambdaIter.Subtyping.Models.RefinementSyntax

/-! # Concrete observation orders for lambda-iter refinement -/

namespace Isotope.LambdaIter.Subtyping.Models

open Isotope.LambdaIter Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless.Refinement

universe u v

variable {S : LambdaIter.Sig.{u}} [LambdaIter.Subtyping S.Ty]

/-- A computation domain distinguishing undefined behavior from divergence.
Undefined behavior is the least element; divergence and returns are otherwise
flat. -/
inductive UBPartial (α : Type v) where
  | ub
  | diverge
  | return (a : α)
deriving DecidableEq

namespace UBPartial

def Le : UBPartial α → UBPartial α → Prop
  | .ub, _ => True
  | .diverge, .diverge => True
  | .return a, .return b => a = b
  | _, _ => False

instance : LE (UBPartial α) := ⟨Le⟩

instance : PartialOrder (UBPartial α) where
  le_refl x := by cases x <;> simp [LE.le, Le]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp_all [LE.le, Le]
  le_antisymm x y := by cases x <;> cases y <;> simp_all [LE.le, Le]

theorem ub_le (x : UBPartial α) : (.ub : UBPartial α) ≤ x := by
  cases x <;> trivial

theorem ub_le_diverge : (.ub : UBPartial α) ≤ .diverge := trivial

end UBPartial

namespace Part

/-- Definedness order on partial values. -/
def Refines (x y : Part α) : Prop := ∀ a, a ∈ x → a ∈ y

theorem refines_refl (x : Part α) : Refines x x := fun _ h => h

theorem refines_trans {x y z : Part α} : Refines x y → Refines y z → Refines x z :=
  fun h k a ha => k a (h a ha)

theorem none_refines (x : Part α) : Refines Part.none x := by
  intro a h
  exact (Part.notMem_none a h).elim

end Part

/-- Add a concrete observation preorder to the proof-relevant syntactic
presentation. All structural operations produce the least observation;
coercion retains both its witness in the presentation and the observation. -/
def observedSyntax (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty))
    (K : Type v) (bottom : K) : Alg.{u, max u v} S where
  El β A := Presentation S.pureEff Ctx.nil R β A × K
  var i := (⟨.bv i, .bv⟩, bottom)
  op f a := (⟨.op f a.1.term, .op a.1.typing⟩, bottom)
  let₁ a b := (⟨.let₁ a.1.term b.1.term, .let₁ a.1.typing b.1.typing⟩, bottom)
  unit := (⟨.unit, .unit⟩, bottom)
  pair a b := (⟨.pair a.1.term b.1.term, .pair a.1.typing b.1.typing⟩, bottom)
  let₂ a c := (⟨.let₂ a.1.term c.1.term, .let₂ a.1.typing c.1.typing⟩, bottom)
  inl a := (⟨.inl a.1.term, .inl a.1.typing⟩, bottom)
  inr b := (⟨.inr b.1.term, .inr b.1.typing⟩, bottom)
  case e l r :=
    (⟨.case e.1.term l.1.term r.1.term, .case e.1.typing l.1.typing r.1.typing⟩, bottom)
  abort a := (⟨.abort a.1.term, .abort a.1.typing⟩, bottom)
  iter a b := (⟨.iter a.1.term b.1.term, .iter a.1.typing b.1.typing⟩, bottom)
  coeSub d a := (⟨a.1.term, .sub a.1.typing d⟩, a.2)

theorem observedSyntax_denote
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty))
    (K : Type v) (bottom : K) {h : HasType S.Instr Ctx.nil β t A} :
    (observedSyntax R K bottom).denote h = (⟨t, h⟩, bottom) := by
  induction h with
  | fv h => simp [Ctx.lookup] at h
  | _ => simp_all [Alg.denote, Alg.Ops.denote, observedSyntax]

def partSyntax (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    Alg.{u, u} S := observedSyntax R (Part (ULift.{u} Unit)) Part.none

def ubPartialSyntax (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    Alg.{u, u} S := observedSyntax R (UBPartial (ULift.{u} Unit)) .ub

def powersetSyntax (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    Alg.{u, u} S := observedSyntax R (Set (ULift.{u} Unit)) ∅

@[reducible] private def observedSyntax_lawful
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty))
    (K : Type v) (bottom : K) (leK : K → K → Prop)
    (hrefl : ∀ x, leK x x) (htrans : ∀ {x y z}, leK x y → leK y z → leK x z) :
    LawfulOrder (observedSyntax R K bottom) := by
  let X := observedSyntax R K bottom
  refine {
    le := fun _ _ a b => Related S.pureEff Ctx.nil R a.1.typing b.1.typing ∧ leK a.2 b.2
    le_refl := fun a => ⟨Related.refl a.1.typing, hrefl _⟩
    le_trans := fun h k => ⟨h.1.trans k.1, htrans h.2 k.2⟩
    op_mono := ?_, let₁_mono := ?_, pair_mono := ?_, let₂_mono := ?_
    inl_mono := ?_, inr_mono := ?_, case_mono := ?_, abort_mono := ?_
    iter_mono := ?_, coeSub_mono := ?_, equiv_sound := ?_ }
  · intro n β f a b h; exact ⟨Related.op h.1, hrefl _⟩
  · intro n β A B a a' b b' ha hb; exact ⟨Related.let₁ ha.1 hb.1, hrefl _⟩
  · intro n β A B a a' b b' ha hb; exact ⟨Related.pair ha.1 hb.1, hrefl _⟩
  · intro n β A B C a a' c c' ha hc; exact ⟨Related.let₂ ha.1 hc.1, hrefl _⟩
  · intro n β A B a a' h; exact ⟨Related.inl h.1, hrefl _⟩
  · intro n β A B b b' h; exact ⟨Related.inr h.1, hrefl _⟩
  · intro n β A B C e e' l l' r r' he hl hr
    exact ⟨Related.case he.1 hl.1 hr.1, hrefl _⟩
  · intro n β C a b h; exact ⟨Related.abort h.1, hrefl _⟩
  · intro n β A B a a' b b' ha hb; exact ⟨Related.iter ha.1 hb.1, hrefl _⟩
  · intro n β A B d a a' h; exact ⟨Related.sub h.1 d, h.2⟩
  · intro n β a b A ha hb h
    rw [observedSyntax_denote, observedSyntax_denote]
    exact ⟨Related.ofEquiv ⟨h⟩, hrefl _⟩

instance partSyntax_lawfulOrder
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    LawfulOrder (partSyntax R) :=
  observedSyntax_lawful R _ _ Part.Refines Part.refines_refl
    (fun h k => Part.refines_trans h k)

instance ubPartialSyntax_lawfulOrder
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    LawfulOrder (ubPartialSyntax R) :=
  observedSyntax_lawful R _ _ (· ≤ ·) le_refl (fun h k => h.trans k)

instance powersetSyntax_lawfulOrder
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    LawfulOrder (powersetSyntax R) :=
  observedSyntax_lawful R _ _ (· ⊆ ·) (fun _ => Set.Subset.rfl)
    (fun h k => h.trans k)

theorem partSyntax_validates
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    LawfulOrder.Validates (partSyntax R) R := by
  intro n β a b A ha hb h
  unfold partSyntax
  rw [observedSyntax_denote, observedSyntax_denote]
  exact ⟨Related.axiom h, Part.refines_refl _⟩

theorem ubPartialSyntax_validates
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    LawfulOrder.Validates (ubPartialSyntax R) R := by
  intro n β a b A ha hb h
  unfold ubPartialSyntax
  rw [observedSyntax_denote, observedSyntax_denote]
  exact ⟨Related.axiom h, le_rfl⟩

theorem powersetSyntax_validates
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    LawfulOrder.Validates (powersetSyntax R) R := by
  intro n β a b A ha hb h
  unfold powersetSyntax
  rw [observedSyntax_denote, observedSyntax_denote]
  exact ⟨Related.axiom h, Set.Subset.rfl⟩

theorem partSyntax_ub_bottom
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty))
    (x : Part (ULift.{u} Unit)) :
    Part.Refines Part.none x := Part.none_refines x

theorem ubPartialSyntax_ub_refines_divergence
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty)) :
    (.ub : UBPartial (ULift.{u} Unit)) ≤ .diverge := UBPartial.ub_le_diverge

theorem powersetSyntax_empty_bottom
    (R : Theory (Φ := S.Instr) (Ctx.nil : Ctx Empty S.Ty))
    (s : Set (ULift.{u} Unit)) :
    (∅ : Set (ULift.{u} Unit)) ⊆ s := Set.empty_subset s

end Isotope.LambdaIter.Subtyping.Models
