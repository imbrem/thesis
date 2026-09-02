import Isotope.LambdaCase.Metatheory.EmbedIter
import Isotope.LambdaIter.Metatheory.Syntax

/-!
# Algebra of locally nameless renaming for lambda-case

The renaming lemmas the equational metatheory needs.  Every one of them is
*transported* rather than reproved: `Tm.embed` is injective and carries
`@[simp]` commutation lemmas for `rename`, `lift`, `underBinder`,
`underTwoBinders` and `instantiate` (see `Isotope/LambdaCase/Syntax.lean`), so
each statement below reduces to its lambda-iter counterpart in
`Isotope/LambdaIter/Metatheory/Syntax.lean` by one `simp`.

The auxiliary `up` of `Isotope/LambdaCase/Syntax.lean` is `private`, so the
statements name lambda-iter's `Syntax.upRen`, which is definitionally equal to
it.  `Isotope/LambdaCase/TypingSubst.lean` already relies on that identification.
-/

namespace Isotope.LambdaCase.LocallyNameless

open Isotope.LambdaIter.LocallyNameless.Syntax (upRen)

namespace Syntax

variable {ν : Type w} {Φ : Type v} {n m : Nat}

@[simp] theorem rename_fv (ρ : Fin n → Fin m) (x : ν) :
    Tm.rename ρ (.fv x : Tm ν Φ n) = .fv x := rfl

@[simp] theorem rename_bv (ρ : Fin n → Fin m) (i : Fin n) :
    Tm.rename ρ (.bv i : Tm ν Φ n) = .bv (ρ i) := rfl

@[simp] theorem rename_op (ρ : Fin n → Fin m) (f : Φ) (a : Tm ν Φ n) :
    Tm.rename ρ (.op f a) = .op f (Tm.rename ρ a) := rfl

@[simp] theorem rename_let₁ (ρ : Fin n → Fin m) (a : Tm ν Φ n)
    (b : Tm ν Φ (n + 1)) :
    Tm.rename ρ (.let₁ a b) = .let₁ (Tm.rename ρ a) (Tm.rename (upRen ρ) b) := rfl

@[simp] theorem rename_unit (ρ : Fin n → Fin m) :
    Tm.rename ρ (.unit : Tm ν Φ n) = .unit := rfl

@[simp] theorem rename_pair (ρ : Fin n → Fin m) (a b : Tm ν Φ n) :
    Tm.rename ρ (.pair a b) = .pair (Tm.rename ρ a) (Tm.rename ρ b) := rfl

@[simp] theorem rename_let₂ (ρ : Fin n → Fin m) (a : Tm ν Φ n)
    (b : Tm ν Φ (n + 2)) :
    Tm.rename ρ (.let₂ a b) =
      .let₂ (Tm.rename ρ a) (Tm.rename (upRen (upRen ρ)) b) := rfl

@[simp] theorem rename_inl (ρ : Fin n → Fin m) (a : Tm ν Φ n) :
    Tm.rename ρ (.inl a) = .inl (Tm.rename ρ a) := rfl

@[simp] theorem rename_inr (ρ : Fin n → Fin m) (a : Tm ν Φ n) :
    Tm.rename ρ (.inr a) = .inr (Tm.rename ρ a) := rfl

@[simp] theorem rename_case (ρ : Fin n → Fin m) (e : Tm ν Φ n)
    (l r : Tm ν Φ (n + 1)) :
    Tm.rename ρ (.case e l r) =
      .case (Tm.rename ρ e) (Tm.rename (upRen ρ) l) (Tm.rename (upRen ρ) r) := rfl

@[simp] theorem rename_abort (ρ : Fin n → Fin m) (a : Tm ν Φ n) :
    Tm.rename ρ (.abort a) = .abort (Tm.rename ρ a) := rfl

/-- Renaming commutes with weakening by one binder. -/
@[simp] theorem rename_lift (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    Tm.rename (upRen ρ) t.lift = (Tm.rename ρ t).lift :=
  Tm.embed_injective (by simp)

/-- Renaming commutes with inserting a binder below the newest one. -/
@[simp] theorem rename_underBinder (ρ : Fin n → Fin m) (t : Tm ν Φ (n + 1)) :
    Tm.rename (upRen (upRen ρ)) t.underBinder =
      (Tm.rename (upRen ρ) t).underBinder :=
  Tm.embed_injective (by simp)

/-- Renaming commutes with inserting a binder below the two newest ones. -/
@[simp] theorem rename_underTwoBinders (ρ : Fin n → Fin m)
    (t : Tm ν Φ (n + 2)) :
    Tm.rename (upRen (upRen (upRen ρ))) t.underTwoBinders =
      (Tm.rename (upRen (upRen ρ)) t).underTwoBinders :=
  Tm.embed_injective (by simp)

/-- Renaming commutes with opening the newest binder. -/
@[simp] theorem rename_instantiate (ρ : Fin n → Fin m) (b : Tm ν Φ (n + 1))
    (a : Tm ν Φ n) :
    Tm.rename ρ (Tm.instantiate b a) =
      Tm.instantiate (Tm.rename (upRen ρ) b) (Tm.rename ρ a) :=
  Tm.embed_injective (by simp)

end Syntax

variable {τ : Type u} [LambdaIter.TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [LambdaIter.HasTy Φ τ]
variable {ε : Type r} [LambdaIter.HasEff Φ ε]

omit [DecidableEq ν] in
/-- Purity is stable under bound renaming. -/
theorem Pure.rename {pureEff : ε} {n m : Nat} (ρ : Fin n → Fin m) :
    {a : Tm ν Φ n} → Pure pureEff a → Pure pureEff (Tm.rename ρ a)
  | _, .fv => .fv
  | _, .bv => .bv
  | _, .op hf ha => .op hf (Pure.rename ρ ha)
  | _, .let₁ ha hb => .let₁ (Pure.rename ρ ha) (Pure.rename _ hb)
  | _, .unit => .unit
  | _, .pair ha hb => .pair (Pure.rename ρ ha) (Pure.rename ρ hb)
  | _, .let₂ ha hb => .let₂ (Pure.rename ρ ha) (Pure.rename _ hb)
  | _, .inl ha => .inl (Pure.rename ρ ha)
  | _, .inr ha => .inr (Pure.rename ρ ha)
  | _, .case he hl hr =>
      .case (Pure.rename ρ he) (Pure.rename _ hl) (Pure.rename _ hr)
  | _, .abort ha => .abort (Pure.rename ρ ha)

end Isotope.LambdaCase.LocallyNameless
