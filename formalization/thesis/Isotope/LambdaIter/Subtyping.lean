import Isotope.LambdaIter.Ty

/-!
# Proof-relevant subtyping for lambda-iter

Subtyping derivations live in `Type`, rather than `Prop`, so denotations may
depend on the chosen coercion derivation.
-/

namespace Isotope.LambdaIter

/-- The operations required of a proof-relevant subtyping discipline. -/
class Subtyping (τ : Type u) [TypeFormers τ] where
  Subty : τ → τ → Type u
  refl (A : τ) : Subty A A
  trans {A B C : τ} : Subty A B → Subty B C → Subty A C
  tensor {A A' B B' : τ} : Subty A A' → Subty B B' →
    Subty (LambdaIter.tensor A B) (LambdaIter.tensor A' B')
  coprod {A A' B B' : τ} : Subty A A' → Subty B B' →
    Subty (LambdaIter.coprod A B) (LambdaIter.coprod A' B')
  empty (A : τ) : Subty LambdaIter.empty A
  unit (A : τ) : Subty A LambdaIter.unit

/-- Proof-relevant subtype witnesses supplied by a `Subtyping` instance. -/
abbrev Subty {τ : Type u} [TypeFormers τ] [Subtyping τ] (A B : τ) : Type u :=
  Subtyping.Subty A B

namespace Subty

def refl [TypeFormers τ] [Subtyping τ] (A : τ) : Subty A A := Subtyping.refl A

def trans [TypeFormers τ] [Subtyping τ] {A B C : τ}
    (f : Subty A B) (g : Subty B C) : Subty A C := Subtyping.trans f g

def tensor [TypeFormers τ] [Subtyping τ] {A A' B B' : τ}
    (f : Subty A A') (g : Subty B B') :
    Subty (LambdaIter.tensor A B) (LambdaIter.tensor A' B') := Subtyping.tensor f g

def coprod [TypeFormers τ] [Subtyping τ] {A A' B B' : τ}
    (f : Subty A A') (g : Subty B B') :
    Subty (LambdaIter.coprod A B) (LambdaIter.coprod A' B') := Subtyping.coprod f g

def empty [TypeFormers τ] [Subtyping τ] (A : τ) : Subty LambdaIter.empty A :=
  Subtyping.empty A

def unit [TypeFormers τ] [Subtyping τ] (A : τ) : Subty A LambdaIter.unit :=
  Subtyping.unit A

end Subty

namespace Ty

/-- The freely generated proof-relevant subtyping derivations for simple types. -/
inductive Subty {α : Type u} : Ty α → Ty α → Type u where
  | refl (A : Ty α) : Subty A A
  | trans {A B C : Ty α} : Subty A B → Subty B C → Subty A C
  | tensor {A A' B B' : Ty α} : Subty A A' → Subty B B' →
      Subty (.tensor A B) (.tensor A' B')
  | coprod {A A' B B' : Ty α} : Subty A A' → Subty B B' →
      Subty (.coprod A B) (.coprod A' B')
  | empty (A : Ty α) : Subty .empty A
  | unit (A : Ty α) : Subty A .unit

instance : Subtyping (Ty α) where
  Subty := Ty.Subty
  refl := Ty.Subty.refl
  trans := Ty.Subty.trans
  tensor := Ty.Subty.tensor
  coprod := Ty.Subty.coprod
  empty := Ty.Subty.empty
  unit := Ty.Subty.unit

section Examples

variable {α : Type u} (A : Ty α)

/-- Reflexivity and reflexivity followed by reflexivity remain distinct data. -/
example : Ty.Subty.refl A ≠ Ty.Subty.trans (Ty.Subty.refl A) (Ty.Subty.refl A) := by
  intro h
  cases h

end Examples

end Ty

end Isotope.LambdaIter
