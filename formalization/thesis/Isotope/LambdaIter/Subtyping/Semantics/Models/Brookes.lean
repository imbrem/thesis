import Isotope.Elgot.Brookes.SeqCst.Iter
import Isotope.LambdaIter.Subtyping.Semantics.Models.Null
import Isotope.LambdaIter.Subtyping.Semantics.Soundness

/-!
# The Brookes model: a shared-memory signature in the trace monad

Every other model in this directory has a *pure* instruction signature, so none
of them exercises the effectful half of `InstructionModel`, and the Brookes
development records the matching gap on its own side: `Brookes c` satisfies
every class the lambda-iter denotational semantics requires — `Monad`,
`LawfulMonad`, `Iterate`, `LawfulElgotMonad` — but no concrete instruction
signature and effect lattice had been chosen, so the two halves never met.

This file closes that gap from both directions.  The signature is the
fine-grained one:

* two base types, `loc` and `val`, interpreted by `Loc` and `Val`;
* two instructions, `read : loc → val` and `write : loc ⊗ val → 1`, denoted by
  `SeqCst.read` and `SeqCst.write` in `SeqCst.Comp Loc Val`;
* both annotated `Eff.impure`, so `denotePure` is vacuous and the effectful
  `denote` is genuinely used.

`brookes_sound` and `brookes_related_sound` then record what
`Semantics.sound` / `Semantics.related_sound` give once the instance exists:
**the lambda-iter equational theory is sound for Brookes trace semantics.**
Nothing further is proved about the equations here; the point is that the
generic soundness theorem is no longer conditional on hypotheses nothing
satisfies.

## Universes

`Brookes` is universe-monomorphic (its alphabet and its value type share one
universe), and `InstructionModel` forces the type model's *interpretation*
universe to equal the monad's.  Hence `Loc Val : Type u` and
`TypeModel.{u, u} (MemTy Loc Val)`.  `Loc` and `Val` are therefore carried as
*phantom* parameters of `Base`, purely so that instance resolution can recover
them from `MemTy Loc Val`; the alternative (`Base : Type 0`, a type model
parameterised by `Loc` and `Val`) typechecks but cannot be an instance.

`TyDen (LambdaIter.unit : MemTy Loc Val)` is *definitionally* the `PUnit` of
`SeqCst.Comp Loc Val PUnit`, so unit-typed denotations meet `SeqCst.obs`,
`SeqCst.den`, `test`, `atom` and `star` with no transport.

## Honest boundary

* **The granularity gap is real and is not closed here.**  `SeqCst.write` is an
  `atom` (`write_eq_atom`), but the *composite* `read ℓ >>= write ℓ'` is not:
  it has two-step traces in which the store changes between the read and the
  write, which no `atom` contains.  That separation is proved downstream, for
  one concrete pair, as `readWrite_ne_den_assign` in
  `Models/Brookes/Compile.lean`; it is not quantified over compilers or over
  terms.  It is why the compilable fragment of that file runs over a
  coarse-atom signature, whose instructions are whole assignments and tests,
  rather than over this one.
* **Soundness only.**  `brookes_sound` is soundness of the equational theory,
  not completeness: nothing here shows that trace-equal terms are provably
  equal.
* **No adequacy.**  The connection between this denotational instance and the
  operational semantics of `Isotope.Elgot.Brookes.SeqCst.Op` is mediated only
  by `Op.opDen_eq_den`, which is about `Com`, not about lambda-iter terms.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics

namespace BrookesModel

open Isotope.Elgot
open Isotope.Elgot.Brookes
open Isotope.LambdaIter (Ctx)
open Isotope.LambdaIter.LocallyNameless (Tm BoundCtx)
open Isotope.LambdaIter.Subtyping.LocallyNameless

universe u w

variable {Loc Val : Type u}

/-! ### The type universe -/

/-- The two base types of the shared-memory signature.  `Loc` and `Val` are
phantom parameters: they do not occur in any constructor, and are present only
so that instance resolution can recover them from the type universe. -/
inductive Base (Loc Val : Type u) : Type u where
  /-- The type of locations. -/
  | loc
  /-- The type of values. -/
  | val
  deriving DecidableEq

/-- Locations denote `Loc`, values denote `Val`. -/
@[reducible] def baseInterp : Base Loc Val → Type u
  | .loc => Loc
  | .val => Val

/-- The type universe of the shared-memory signature. -/
@[reducible] def MemTy (Loc Val : Type u) : Type u := LambdaIter.Ty (Base Loc Val)

/-- The type of locations, as an object-language type. -/
abbrev locTy : MemTy Loc Val := .base .loc

/-- The type of values, as an object-language type. -/
abbrev valTy : MemTy Loc Val := .base .val

/-- The shared-memory type model. -/
@[reducible] def typeModel : TypeModel.{u, u} (MemTy Loc Val) :=
  Free.typeModel (baseInterp (Loc := Loc) (Val := Val))

attribute [instance] typeModel

instance : LawfulTypeModel.{u, u} (MemTy Loc Val) := Free.lawfulTypeModel _

@[simp] theorem tyDen_loc : TyDen (locTy : MemTy Loc Val) = Loc := rfl

@[simp] theorem tyDen_val : TyDen (valTy : MemTy Loc Val) = Val := rfl

theorem tyDen_unit : TyDen (LambdaIter.unit : MemTy Loc Val) = PUnit := rfl

/-! ### The instruction signature -/

/-- The fine-grained shared-memory instruction signature: a single-location
read and a single-location write. -/
inductive Instr (Loc Val : Type u) : Type u where
  /-- Read the value stored at a location. -/
  | read
  /-- Write a value to a location. -/
  | write
  deriving DecidableEq

instance : LambdaIter.HasTy (Instr Loc Val) (MemTy Loc Val) where
  src
    | .read => locTy
    | .write => .tensor locTy valTy
  trg
    | .read => valTy
    | .write => .unit

/-- Both memory instructions are impure. -/
instance : LambdaIter.HasEff (Instr Loc Val) Eff where
  eff _ := Eff.impure

@[simp] theorem eff_eq (f : Instr Loc Val) :
    (LambdaIter.instrEff f : Eff) = Eff.impure := rfl

/-- No memory instruction is pure. -/
theorem eff_ne_bot (f : Instr Loc Val) : (LambdaIter.instrEff f : Eff) ≠ (⊥ : Eff) := by
  simp

/-! ### The instruction model -/

/-- `read` denotes `SeqCst.read`, `write` denotes `SeqCst.write`. -/
def instrDenote [DecidableEq Loc] : (f : Instr Loc Val) →
    Free.interp (baseInterp (Loc := Loc) (Val := Val)) (LambdaIter.instrSrc f) →
      SeqCst.Comp Loc Val
        (Free.interp (baseInterp (Loc := Loc) (Val := Val)) (LambdaIter.instrTrg f))
  | .read, l => SeqCst.read l
  | .write, p => SeqCst.write p.1 p.2

/-- **The Brookes trace monad models the shared-memory signature.**  This is
the first `InstructionModel` instance in the development whose instructions are
genuinely effectful. -/
instance instructionModel [DecidableEq Loc] :
    InstructionModel (Instr Loc Val) (MemTy Loc Val) Eff (SeqCst.Comp Loc Val) where
  denote f := instrDenote f
  denotePure f hf := absurd hf (eff_ne_bot f)
  denote_pure f hf := absurd hf (eff_ne_bot f)

@[simp] theorem instrDenote_read [DecidableEq Loc] (l : Loc) :
    instrDenote (Val := Val) .read l = SeqCst.read l := rfl

@[simp] theorem instrDenote_write [DecidableEq Loc] (p : Loc × Val) :
    instrDenote .write p = SeqCst.write p.1 p.2 := rfl

/-! ### Unfolding instruction denotations -/

section Op

variable {ν : Type w} [DecidableEq ν] [DecidableEq Loc]

/-- The denotation of an instruction application is the source denotation bound
into `instrDenote`.  This is the first time in the development that the
effectful field of `InstructionModel` is unfolded at a concrete monad. -/
theorem denote_op {Γ : Ctx ν (MemTy Loc Val)} {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n} {a : Tm ν (Instr Loc Val) n} {f : Instr Loc Val}
    (ha : HasType (Instr Loc Val) Γ β a (LambdaIter.instrSrc f))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) (.op ha) γ ρ
      = denote (m := SeqCst.Comp Loc Val) (ε := Eff) ha γ ρ >>= instrDenote f := by
  simp only [denote]
  rfl

/-- A `read` application denotes a bind into `SeqCst.read`. -/
theorem denote_op_read {Γ : Ctx ν (MemTy Loc Val)} {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n} {a : Tm ν (Instr Loc Val) n}
    (ha : HasType (Instr Loc Val) Γ β a locTy) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) (.op (f := Instr.read) ha) γ ρ
      = denote (m := SeqCst.Comp Loc Val) (ε := Eff) ha γ ρ >>= SeqCst.read := by
  simp only [denote]
  rfl

/-- A `write` application denotes a bind into `SeqCst.write`. -/
theorem denote_op_write {Γ : Ctx ν (MemTy Loc Val)} {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n} {a : Tm ν (Instr Loc Val) n}
    (ha : HasType (Instr Loc Val) Γ β a (.tensor locTy valTy))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) (.op (f := Instr.write) ha) γ ρ
      = denote (m := SeqCst.Comp Loc Val) (ε := Eff) ha γ ρ
          >>= fun p => SeqCst.write p.1 p.2 := by
  simp only [denote]
  rfl

end Op

/-! ### `write` is an atom -/

/-- `SeqCst.write` is the atomic action that updates one location.  The two
sides are *not* definitionally equal — `write` closes
`{p | ∃ μ, p.1 = [(μ, update μ ℓ v)]}` while `atom R` closes
`{q | ∃ μ ν, R μ ν ∧ q.1 = [(μ, ν)]}` — but the generated sets coincide. -/
theorem write_eq_atom [DecidableEq Loc] (l : Loc) (v : Val) :
    (SeqCst.write l v : SeqCst.Comp Loc Val PUnit)
      = SeqCst.atom (fun μ σ ↦ σ = Function.update μ l v) := by
  apply Brookes.ext_mem
  intro t x
  rw [SeqCst.mem_write_iff, SeqCst.mem_atom_iff]
  constructor
  · rintro ⟨μ, hr⟩
    exact ⟨μ, _, rfl, hr⟩
  · rintro ⟨μ, σ, rfl, hr⟩
    exact ⟨μ, hr⟩

/-- A write is observed exactly as a single-location update. -/
@[simp] theorem obs_write [DecidableEq Loc] (l : Loc) (v : Val)
    {μ σ : SeqCst.Store Loc Val} :
    SeqCst.obs (SeqCst.write l v) μ σ ↔ σ = Function.update μ l v := by
  rw [write_eq_atom]
  exact SeqCst.obs_atom

/-! ### Soundness of the lambda-iter equational theory for trace semantics -/

section Soundness

variable {ν : Type w} [DecidableEq ν] [DecidableEq Loc]

/-- **The lambda-iter equational theory is sound for Brookes trace semantics.**
Every proof-relevant typed equation between shared-memory programs is an
equality of trace sets. -/
theorem brookes_sound {Γ : Ctx ν (MemTy Loc Val)} {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n}
    {a b : Tm ν (Instr Loc Val) n} {A : MemTy Loc Val}
    {ha : HasType (Instr Loc Val) Γ β a A} {hb : HasType (Instr Loc Val) Γ β b A}
    (d : TypedEquiv.Deriv (⊥ : Eff) Γ ha hb)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) ha γ ρ
      = denote (m := SeqCst.Comp Loc Val) (ε := Eff) hb γ ρ :=
  sound d γ ρ

/-- The truncated form of `brookes_sound`. -/
theorem brookes_related_sound {Γ : Ctx ν (MemTy Loc Val)} {n : Nat}
    {β : BoundCtx (MemTy Loc Val) n}
    {a b : Tm ν (Instr Loc Val) n} {A : MemTy Loc Val}
    {ha : HasType (Instr Loc Val) Γ β a A} {hb : HasType (Instr Loc Val) Γ β b A}
    (h : TypedEquiv.Related (⊥ : Eff) Γ ha hb)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := SeqCst.Comp Loc Val) (ε := Eff) ha γ ρ
      = denote (m := SeqCst.Comp Loc Val) (ε := Eff) hb γ ρ :=
  related_sound h γ ρ

/-- Soundness at closed terms: related closed programs denote the same set of
traces. -/
theorem brookes_related_sound_closed
    {a b : Tm Empty (Instr Loc Val) 0} {A : MemTy Loc Val}
    {ha : HasType (Instr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) .nil a A}
    {hb : HasType (Instr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) .nil b A}
    (h : TypedEquiv.Related (⊥ : Eff) (.nil : Ctx Empty (MemTy Loc Val)) ha hb) :
    denoteClosed (m := SeqCst.Comp Loc Val) (ε := Eff) ha
      = denoteClosed (m := SeqCst.Comp Loc Val) (ε := Eff) hb :=
  related_sound h PUnit.unit PUnit.unit

/-- **Observational soundness.**  At result type `1`, a closed lambda-iter
program denotes an element of `SeqCst.Comp Loc Val PUnit` — the same type as
`SeqCst.den` — with no transport, so `SeqCst.obs` applies directly, and related
programs relate exactly the same initial and final stores. -/
theorem brookes_obs_congr
    {a b : Tm Empty (Instr Loc Val) 0}
    {ha : HasType (Instr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) .nil a
      LambdaIter.unit}
    {hb : HasType (Instr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) .nil b
      LambdaIter.unit}
    (h : TypedEquiv.Related (⊥ : Eff) (.nil : Ctx Empty (MemTy Loc Val)) ha hb)
    (μ σ : SeqCst.Store Loc Val) :
    SeqCst.obs (denoteClosed (m := SeqCst.Comp Loc Val) (ε := Eff) ha) μ σ
      ↔ SeqCst.obs (denoteClosed (m := SeqCst.Comp Loc Val) (ε := Eff) hb) μ σ := by
  rw [brookes_related_sound_closed h]

end Soundness

end BrookesModel

end Isotope.LambdaIter.Subtyping.Semantics
