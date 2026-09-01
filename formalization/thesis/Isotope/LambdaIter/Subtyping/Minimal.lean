import Isotope.LambdaIter.Semantics.Model

/-!
# A proof-irrelevant minimal subtyping experiment

This module supplies a parallel type universe whose preorder is generated only
by reflexivity, `0 ≤ A`, `A ≤ 1`, transitivity, and congruence for tensor and
coproduct.  Unlike `Ty.Subty`, derivations are propositionally truncated.
-/

namespace Isotope.LambdaIter

/-- A separate copy of the freely generated types, used to experiment with a
minimal, proof-irrelevant subtyping discipline without changing the existing
proof-relevant development. -/
structure MinimalTy (α : Type u) where
  val : Ty α
  deriving DecidableEq, Repr

namespace MinimalTy

instance : TypeFormers (MinimalTy α) where
  tensor A B := ⟨.ty.tensor A.val B.val⟩
  unit := ⟨.ty.unit⟩
  coprod A B := ⟨.ty.coprod A.val B.val⟩
  empty := ⟨.ty.empty⟩

/-- The least proposition-valued relation containing the two boundedness
rules and closed under the object-language type formers. -/
inductive Le {α : Type u} : MinimalTy α → MinimalTy α → Prop where
  | refl (A) : Le A A
  | trans : Le A B → Le B C → Le A C
  | tensor : Le A A' → Le B B' → Le (tensor A B) (tensor A' B')
  | coprod : Le A A' → Le B B' → Le (coprod A B) (coprod A' B')
  | empty (A) : Le empty A
  | unit (A) : Le A unit

/-- A universe lift makes propositionally truncated witnesses fit the
universe-polymorphic, proof-relevant `Subtyping` interface. -/
abbrev Witness {α : Type u} (A B : MinimalTy α) : Type u := PLift (Le A B)

instance : Subtyping (MinimalTy α) where
  Subty := Witness
  refl A := ⟨.Le.refl A⟩
  trans f g := ⟨.Le.trans f.down g.down⟩
  tensor f g := ⟨.Le.tensor f.down g.down⟩
  coprod f g := ⟨.Le.coprod f.down g.down⟩
  empty A := ⟨.Le.empty A⟩
  unit A := ⟨.Le.unit A⟩

instance subtySubsingleton (A B : MinimalTy α) : Subsingleton (Subty A B) :=
  inferInstance

theorem subty_unique {A B : MinimalTy α} (f g : Subty A B) : f = g :=
  Subsingleton.elim _ _

end MinimalTy

namespace Semantics

section Minimal

variable {α : Type u} [TypeModel.{u, v} (MinimalTy α)]

/-- In the minimal discipline, coercion semantics is independent of the
chosen construction of a subtype witness. -/
theorem minimal_coe_proof_irrel {A B : MinimalTy α} (f g : Subty A B) :
    coeSub f = coeSub g := by
  rw [MinimalTy.subty_unique f g]

/-- In a lawful model, sequential coercions equal the coercion denoted by any
witness of the composite judgment. -/
theorem minimal_coe_comp [LawfulTypeModel.{u, v} (MinimalTy α)]
    {A B C : MinimalTy α} (f : Subty A B) (g : Subty B C) (h : Subty A C) :
    coeSub g ∘ coeSub f = coeSub h := by
  rw [← LawfulTypeModel.coe_trans f g]
  exact minimal_coe_proof_irrel (Subty.trans f g) h

end Minimal

end Semantics

end Isotope.LambdaIter
