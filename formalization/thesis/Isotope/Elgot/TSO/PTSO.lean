import Isotope.Elgot.TSO.Ops
import Isotope.CategoryTheory.Ide
import Mathlib.CategoryTheory.Category.KleisliCat

/-!
# `PTSO = Ide(Set_TSO, pflush)`

The paper's final categorical model for TSO weak memory
(`denotational-semantics-of-ssa.tex` L4907-5008): since `pflush` is idempotent but not the
identity, one passes to the idempotent envelope, in which `pflush_A` *is* the identity at `A`.

## Honest boundary

Only the **category** is constructed.  The inheritance chain of L4940-5006 — coproducts,
Elgot structure, premonoidal, distributive, Freyd — is not formalised, so nothing here shows
that `PTSO` is an SSA model; the paper asserts those properties for `d = pflush` without a
displayed proof.

The `pflush` sandwich equations of `Isotope.Elgot.TSO.Ops` carry the same *reasoning* content
as the envelope for the concrete operations: `pflush ≫ₖ read x = read x` and friends say
directly that a stray flush around an instruction is invisible, which is what the envelope
was introduced to arrange.
-/

universe u

namespace Isotope.Elgot.TSO

open CategoryTheory Isotope.Pomset Isotope.Elgot

/-- `pflush` as an idempotent family on the Kleisli category `Set_TSO` of `TSO`. -/
def pflushFamily (Loc Val : Type u) : IdemFamily (KleisliCat (TSO Loc Val)) where
  d _ := pflush
  idem _ := pflush_kcomp_pflush

variable {Loc Val : Type u}

/-- The paper's `PTSO = Ide(Set_TSO, pflush)` (L4907-4912). -/
abbrev PTSO (Loc Val : Type u) : Type (u + 1) := Ide (pflushFamily Loc Val)

example : Category (PTSO Loc Val) := inferInstance

/-- The identity of `PTSO` at `A` is `pflush_A`, not `pure` (L4913-4918). -/
theorem PTSO.id_eq (X : PTSO Loc Val) : (𝟙 X : X ⟶ X).1 = pflush := rfl

/-- Every Kleisli arrow of `Set_TSO` sandwiched by `pflush` is a morphism of `PTSO`, which is
the paper's `PTSO(A,B) = {pflush_A ; f ; pflush_B}` presentation of the hom-sets. -/
def PTSO.homMk {X Y : PTSO Loc Val} (f : X.as ⟶ Y.as) : X ⟶ Y := Ide.homMk _ f

theorem PTSO.homMk_eq {X Y : PTSO Loc Val} (f : X.as ⟶ Y.as) :
    (PTSO.homMk f).1 = sandwich f := rfl

end Isotope.Elgot.TSO
