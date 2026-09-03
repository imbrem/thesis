import Isotope.LambdaSSA.Translation.Compile.Subtyping
import Isotope.LambdaSSA.Translation.Frontend.Closed.Subtyping
import Isotope.LambdaIter.Subtyping.Named.ToLocallyNameless
import Isotope.LambdaCase.Subtyping
import Isotope.LambdaSeq.Subtyping

/-! # Proof-relevant subtyping frontends for lambda-SSA compilation -/

namespace Isotope.LambdaSSA.Translation.Frontend.Subtyping

open Isotope.LambdaIter

universe u w q

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
variable {Φ : Type q} [HasTy Φ τ]

namespace LambdaIter.LocallyNameless

def compile (t : Isotope.LambdaIter.LocallyNameless.Tm Empty Φ n) :
    LambdaSSA.Region Φ := Isotope.LambdaSSA.Translation.Compile.compile 0 t

def compile_hasType {β : Isotope.LambdaIter.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    LambdaSSA.Subtyping.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) (compile t) [A] :=
  Isotope.LambdaSSA.Translation.Compile.Subtyping.compile_hasType h
    (by simp [LambdaSSA.At])

end LambdaIter.LocallyNameless

namespace LambdaCase.LocallyNameless

def compile (t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n) :
    LambdaSSA.Region Φ := LambdaIter.LocallyNameless.compile t.embed

def compile_hasType {β : Isotope.LambdaCase.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaCase.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    LambdaSSA.Subtyping.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) (compile t) [A] :=
  LambdaIter.LocallyNameless.compile_hasType h.embed

end LambdaCase.LocallyNameless

namespace LambdaSeq.LocallyNameless

def compile (t : Isotope.LambdaSeq.LocallyNameless.Tm Empty Φ n) :
    LambdaSSA.Region Φ := LambdaIter.LocallyNameless.compile t.embedIter

def compile_hasType {β : Isotope.LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : Isotope.LambdaSeq.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Isotope.LambdaSeq.Subtyping.LocallyNameless.HasType Φ
      (Ctx.nil : Ctx Empty τ) β t A) :
    LambdaSSA.Subtyping.Region.HasType
      (LambdaSSA.LocallyNameless.ToDeBruijn.context β) (compile t) [A] :=
  LambdaIter.LocallyNameless.compile_hasType h.embedIter

end LambdaSeq.LocallyNameless

section Named

variable {ν : Type w} [DecidableEq ν]

/-- Lower a closed proof-relevant named derivation to a closed locally
nameless derivation, retaining every subtyping witness.  This is public so
the semantic frontend can state and prove agreement with the chosen lowering. -/
noncomputable def lowerNamed
    {t : Isotope.LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    Σ t' : Isotope.LambdaIter.LocallyNameless.Tm Empty Φ 0,
      Isotope.LambdaIter.Subtyping.LocallyNameless.HasType Φ
        (Ctx.nil : Ctx Empty τ) .nil t' A :=
  Closed.Subtyping.erase
    (Isotope.LambdaIter.Subtyping.Named.ToLocallyNameless.translateHasTypeClosed h)

namespace LambdaIter.Named

noncomputable def compileTyped {t : Isotope.LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    LambdaSSA.Region Φ := LambdaIter.LocallyNameless.compile (lowerNamed h).1

noncomputable def compileTyped_hasType {t : Isotope.LambdaIter.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaIter.Subtyping.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    LambdaSSA.Subtyping.Region.HasType [] (compileTyped h) [A] :=
  LambdaIter.LocallyNameless.compile_hasType (lowerNamed h).2

end LambdaIter.Named

namespace LambdaCase.Named

noncomputable def compileTyped {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Subtyping.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    LambdaSSA.Region Φ := LambdaIter.Named.compileTyped h.embed

noncomputable def compileTyped_hasType {t : Isotope.LambdaCase.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaCase.Subtyping.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    LambdaSSA.Subtyping.Region.HasType [] (compileTyped h) [A] :=
  LambdaIter.Named.compileTyped_hasType h.embed

end LambdaCase.Named

namespace LambdaSeq.Named

noncomputable def compileTyped {t : Isotope.LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaSeq.Subtyping.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    LambdaSSA.Region Φ := LambdaIter.Named.compileTyped h.embedIter

noncomputable def compileTyped_hasType {t : Isotope.LambdaSeq.Named.Tm ν Φ} {A : τ}
    (h : Isotope.LambdaSeq.Subtyping.Named.HasType (Ctx.nil : Ctx ν τ) t A) :
    LambdaSSA.Subtyping.Region.HasType [] (compileTyped h) [A] :=
  LambdaIter.Named.compileTyped_hasType h.embedIter

end LambdaSeq.Named
end Named

end Isotope.LambdaSSA.Translation.Frontend.Subtyping
