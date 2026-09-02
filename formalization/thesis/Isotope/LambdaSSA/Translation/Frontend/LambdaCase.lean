import Isotope.LambdaCase.Typing
import Isotope.LambdaSSA.Translation.Frontend.Core
import Isotope.LambdaSSA.Translation.Frontend.Closed
import Isotope.LambdaSSA.Translation.Frontend.NamedToLocallyNameless

/-! # Lambda-case frontends for lambda-SSA -/

namespace Isotope.LambdaSSA.Translation.Frontend.LambdaCase

open Isotope.LambdaIter

namespace LocallyNameless

/-- Compile an exact locally nameless lambda-case term with no free names. -/
def compile (t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n) :
    LambdaSSA.Region Φ :=
  Core.compile t.embed

variable {τ : Type u} [TypeFormers τ]
variable {Φ : Type q} [HasTy Φ τ]

/-- Exact typing is preserved by the lambda-case frontend. -/
def compile_hasType {β : Isotope.LambdaCase.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaCase.LocallyNameless.HasType Φ
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β t A) :
    LambdaSSA.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) (compile t) [A] :=
  Core.compile_hasType h.embed

end LocallyNameless

namespace Named

open Isotope.LambdaIter

/-- Close a named lambda-case term over the empty name type by resolving its
binders to de Bruijn indices. -/
def lowerAt : (n : Nat) → Isotope.LambdaCase.Named.Tm Empty Φ →
    Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n
  | _, .var x => nomatch x
  | n, .op f a => .op f (lowerAt n a)
  | n, .let₁ x a b => by
      cases x with
      | none => exact .let₁ (lowerAt n a) (lowerAt (n + 1) b)
      | some x => exact nomatch x
  | _, .unit => .unit
  | n, .pair a b => .pair (lowerAt n a) (lowerAt n b)
  | n, .let₂ x y a b => by
      cases x with
      | some x => exact nomatch x
      | none => cases y with
        | some y => exact nomatch y
        | none => exact .let₂ (lowerAt n a) (lowerAt (n + 2) b)
  | n, .inl a => .inl (lowerAt n a)
  | n, .inr a => .inr (lowerAt n a)
  | n, .case e x l y r => by
      cases x with
      | some x => exact nomatch x
      | none => cases y with
        | some y => exact nomatch y
        | none => exact .case (lowerAt n e) (lowerAt (n + 1) l) (lowerAt (n + 1) r)
  | n, .abort a => .abort (lowerAt n a)

def lower (t : Isotope.LambdaCase.Named.Tm Empty Φ) :
    Isotope.LambdaCase.LocallyNameless.Tm Empty Φ 0 := lowerAt 0 t

def compile (t : Isotope.LambdaCase.Named.Tm Empty Φ) : LambdaSSA.Region Φ :=
  LocallyNameless.compile (lower t)

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]

noncomputable def closedTerm {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    Σ t' : LambdaIter.LocallyNameless.Tm Empty Φ 0,
      LambdaIter.LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ) .nil t' A :=
  Classical.choice ((NamedToLocallyNameless.translateHasTypeClosed h.embed).map
    Closed.erase)

/-- Compile any well-typed closed named lambda-case term. -/
noncomputable def compileTyped {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    LambdaSSA.Region Φ := Core.compile (closedTerm h).1

def compileTyped_hasType {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    LambdaSSA.Region.HasType [] (compileTyped h) [A] :=
  Core.compile_hasType (closedTerm h).2

end Named

end Isotope.LambdaSSA.Translation.Frontend.LambdaCase
