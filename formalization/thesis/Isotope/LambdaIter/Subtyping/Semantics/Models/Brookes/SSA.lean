import Isotope.LambdaIter.Subtyping.Semantics.Models.Brookes.Compile
import Isotope.LambdaSSA.Translation.Compile
import Isotope.LambdaSSA.Translation.ANF.Elaboration.DirectElaborate
import Isotope.LambdaSSA.Semantics.Monadic.Region

/-!
# From the compilable fragment to SSA: how far the bridge reaches

`Models/Brookes/Compile.lean` proves `den_compile`, identifying the Brookes trace
denotation of a compiled command with the lambda-iter denotation of the
derivation it came from.  `Isotope/LambdaSSA/Translation/Compile.lean` compiles a
lambda-iter term the other way, into an SSA region, and proves it *well typed*
and nothing more.  This file asks how much of the square

      lambda-iter term  --denote-->  Brookes traces
             |                             |
          compile                       compile
             v                             v
        SSA region     --denote-->        ???

closes on the present development, and answers honestly: **the typing leg
entirely, the semantic leg only for loop- and branch-free programs.**

## The generic half: `SSABridge`

`Straight` is the fragment of ANF that `ToSSA` compiles without emitting a
control-flow graph — no `case`, no `iter`, so only `ret`, `let₁` of an atom, and
`let₂`.  For it, `straight_denotes` is exactly the restriction to that fragment
of the lemma the development is missing:

    RegionDenotes ε hR (fun ρ => Direct.denoteProgram h ⋆ (envToBound ρ)
                                   >>= fun a => pure (labelInject result hout a))

It holds over any lawful monad with an `Iterate` instance and any type model,
with `envToBound` reindexing an SSA environment as a lambda-iter bound
environment and `atom_denotes` handling the atoms.  `Straight` is closed under `programRename`
and `bind`, so administrative elaboration keeps a branch-free source term inside
it.

## The Brookes half

* `exactDeriv` extracts, from a `Compilable` derivation of the *subtyping*
  judgment, the coercion-free derivation of `LambdaIter.LocallyNameless.HasType`
  the SSA frontend consumes; `toGeneric_exactDeriv` shows nothing is lost, since
  compilable derivations never use `sub`.
* **Typing composes for the whole fragment.**  `compile_region_hasType` and
  `compileClosed_region_hasType`.
* **The ANF leg composes for the whole fragment.**  `anfDen_eq_den_compile`:
  the direct denotation of the elaborated ANF program *is* `SeqCst.den` of the
  compiled command.  It inherits the operational payoff — `opObs_anfDen` and
  `anf_fullAbstraction` restate `Op.opObs` and `Op.OpCtxLe` full abstraction
  against the ANF denotation.
* **The SSA leg composes for the loop-free fragment.**  `Loopfree` cuts
  `Compilable` down to `skip`, `assign` and `;`, and
  `loopfree_region_denotes` states that the compiled *region* denotes the trace
  set of the compiled command, injected at the result label.

## What is missing, and why

For `ite` and `wh` the SSA leg is open.  `ToSSA.simpleProgram` compiles an ANF
`case` to a one-block CFG and an ANF `iter` to a *two*-block CFG with a
`case (var 0)` dispatcher and a `renameVars (lift Nat.succ)` shift in the
continuation; recovering the source `Elgot.iter` from the `iter` that
`RegionDenotes.cfg` builds needs uniformity and codiagonal plus a naturality
theory for `renameVars` that does not exist here.  That is the whole content of
the missing general lemma, `ANF.ToSSA.program_denotes`, of which
`straight_denotes` below is the CFG-free special case.

Two further obstacles are structural rather than a matter of more proof, and are
the reason even the loop-free result is phrased as a `RegionDenotes` rather than
as an equation with `SeqCst.den`.

* **`Region.denote` is not a function of the region.**  It is a
  `Classical.choice` pick out of `regionDenotes_exists`, and
  `Monadic.RegionTypingCoherent`, the assumption making it unique, is documented
  in `Semantics/Monadic/Coherence.lean` as *not* derivable from the raw typing
  relation.
* **`LabelDen L` is a colimit, not a sum.**  Even at `L = [unit]`, comparing it
  with the `PUnit` of `SeqCst.Comp Loc Val PUnit` would need an inverse for
  `labelInject 0`, which does not exist on this branch.  So the label injection
  stays in the statement.

Compiling *out* of SSA is further away still: `Translation/FromSSA.lean` returns
`Nonempty` typing derivations rather than derivations, so `denote` cannot be
applied to its output at all.

Nothing below is conditional: every declaration in this file is proved outright.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics

/-! ## Generic: the CFG-free fragment of ANF-to-SSA compilation -/

namespace SSABridge

open Isotope.Elgot
open Isotope.LambdaIter (TypeFormers Subtyping HasTy HasEff Ctx)
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Translation
open Isotope.LambdaSSA.LocallyNameless.ToDeBruijn (context)

universe u v q r

section Syntax

variable {Φ : Type q}

/-- ANF programs with no `case` and no `iter`: exactly the programs `ToSSA`
compiles without emitting a control-flow graph. -/
inductive Straight : {n : Nat} → ANF.Program Empty Φ n → Prop
  | ret {n : Nat} (a : ANF.Atom Empty Φ n) : Straight (.ret a)
  | let₁ {n : Nat} (a : ANF.Atom Empty Φ n) {b : ANF.Program Empty Φ (n + 1)} :
      Straight b → Straight (.let₁ (.atom a) b)
  | let₂ {n : Nat} (a : ANF.Atom Empty Φ n) {b : ANF.Program Empty Φ (n + 2)} :
      Straight b → Straight (.let₂ a b)

/-- Renaming bound variables keeps a program branch-free. -/
theorem straight_programRename {n : Nat} {p : ANF.Program Empty Φ n} (hs : Straight p) :
    ∀ {k : Nat} (σ : Fin n → Fin k), Straight (ANF.Elaboration.programRename σ p) := by
  induction hs with
  | ret a => intro k σ; exact .ret _
  | let₁ a hb ih => intro k σ; exact .let₁ _ (ih _)
  | let₂ a hb ih => intro k σ; exact .let₂ _ (ih _)

/-- Sequencing keeps a program branch-free. -/
theorem straight_bind {n : Nat} {p : ANF.Program Empty Φ n} (hs : Straight p) :
    ∀ {q : ANF.Program Empty Φ (n + 1)}, Straight q →
      Straight (ANF.Elaboration.bind p q) := by
  induction hs with
  | ret a => intro q hq; exact .let₁ _ hq
  | let₁ a hb ih => intro q hq; exact .let₁ _ (ih (straight_programRename hq _))
  | let₂ a hb ih => intro q hq; exact .let₂ _ (ih (straight_programRename hq _))

end Syntax

section Semantics

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

/-- Reindex an SSA environment as a lambda-iter bound environment. -/
def envToBound : {n : Nat} → {β : LambdaIter.LocallyNameless.BoundCtx τ n} →
    Env (τ := τ) (context β) → BoundDen β
  | 0, .nil, _ => PUnit.unit
  | _ + 1, .snoc _ _, ρ => (envToBound ρ.1, ρ.2)

/-- The two environment lookups agree. -/
theorem get_envToBound : {n : Nat} → {β : LambdaIter.LocallyNameless.BoundCtx τ n} →
    (ρ : Env (τ := τ) (context β)) → (i : Fin n) →
    BoundDen.get (envToBound ρ) i
      = Env.get ρ i.val
          (LambdaSSA.LocallyNameless.ToDeBruijn.getElem_context β i)
  | 0, .nil, _, i => Fin.elim0 i
  | _ + 1, .snoc β A, ρ, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact get_envToBound ρ.1 j

omit [LawfulMonad m] [LawfulElgotMonad m] in
theorem denoteAtom_bv {n : Nat} {β : LambdaIter.LocallyNameless.BoundCtx τ n} (i : Fin n)
    (ρ : Env (τ := τ) (context β)) :
    ANF.Elaboration.Direct.denoteAtom (ε := ε) (m := m)
        (ANF.Atom.HasType.bv (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (β := β) (i := i))
        PUnit.unit (envToBound ρ)
      = pure (Env.get ρ i.val
          (LambdaSSA.LocallyNameless.ToDeBruijn.getElem_context β i)) := by
  simp only [ANF.Elaboration.Direct.denoteAtom]
  rw [get_envToBound]

omit [LawfulMonad m] [LawfulElgotMonad m] in
/-- The SSA term compiled from an ANF atom denotes that atom. -/
theorem atom_denotes {n : Nat} {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : ANF.Atom Empty Φ n} {A : τ}
    (ha : ANF.Atom.HasType (Ctx.nil : Ctx Empty τ) β a A) :
    ∀ h : LambdaSSA.Tm.HasType (context β) (ANF.ToSSA.atom a) A,
      Denotes (m := m) ε h
        (fun ρ => ANF.Elaboration.Direct.denoteAtom (ε := ε) (m := m) ha PUnit.unit
          (envToBound ρ)) := by
  induction ha with
  | fv hx => cases hx
  | bv => intro h; simp only [denoteAtom_bv]; exact .var _
  | op ha ih => intro h; exact .op (ih (ANF.ToSSA.atom_hasType ha))
  | unit => intro h; exact .unit
  | pair ha hb iha ihb =>
      intro h
      exact .pair (iha (ANF.ToSSA.atom_hasType ha)) (ihb (ANF.ToSSA.atom_hasType hb))
  | inl ha ih => intro h; exact .inl (ih (ANF.ToSSA.atom_hasType ha))
  | inr ha ih => intro h; exact .inr (ih (ANF.ToSSA.atom_hasType ha))
  | abort ha ih => intro h; exact .abort (ih (ANF.ToSSA.atom_hasType ha))

omit [LawfulElgotMonad m] in
/-- **Semantic preservation of ANF-to-SSA compilation, on the CFG-free
fragment.**  This is the restriction to `Straight` of the general lemma the
development is missing; `ret`, `let₁` of an atom and `let₂` compile to `br`,
`let₁` and `let₂`, with no `cfg` and hence no fixed point to contract. -/
theorem straight_denotes {n : Nat} {p : ANF.Program Empty Φ n} (hs : Straight p) :
    ∀ {β : LambdaIter.LocallyNameless.BoundCtx τ n} {A : τ}
      (h : ANF.Program.HasType (Ctx.nil : Ctx Empty τ) β p A)
      {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A)
      (hR : LambdaSSA.Region.HasType (context β) (ANF.ToSSA.program result p) L),
      RegionDenotes (m := m) ε hR
        (fun ρ => ANF.Elaboration.Direct.denoteProgram (ε := ε) (m := m) h PUnit.unit
          (envToBound ρ) >>= fun a => pure (labelInject result hout a)) := by
  induction hs with
  | ret a =>
      intro β A h L result hout hR
      cases h with
      | ret ha =>
        exact .br (h := hout) (atom_denotes ha (ANF.ToSSA.atom_hasType ha))
  | let₁ a hb ih =>
      intro β A h L result hout hR
      cases h with
      | let₁ hi hbody =>
        cases hi with
        | atom ha =>
          have e : (fun ρ : Env (τ := τ) (context β) =>
              ANF.Elaboration.Direct.denoteProgram (ε := ε) (m := m)
                (ANF.Program.HasType.let₁ (ANF.Instr.HasType.atom ha) hbody) PUnit.unit
                (envToBound ρ) >>= fun v => pure (labelInject result hout v))
            = (fun ρ =>
              (fun ρ' => ANF.Elaboration.Direct.denoteAtom (ε := ε) (m := m) ha PUnit.unit
                (envToBound ρ')) ρ >>= fun v =>
                  (fun ρ' => ANF.Elaboration.Direct.denoteProgram (ε := ε) (m := m) hbody
                    PUnit.unit (envToBound ρ') >>= fun w =>
                      pure (labelInject result hout w)) (ρ, v)) := by
            funext ρ
            simp only [ANF.Elaboration.Direct.denoteProgram,
              ANF.Elaboration.Direct.denoteInstr, bind_assoc]
            rfl
          rw [e]
          exact .let₁ (atom_denotes ha (ANF.ToSSA.atom_hasType ha))
            (ih hbody hout (ANF.ToSSA.program_hasType hbody hout))
  | let₂ a hb ih =>
      intro β A h L result hout hR
      cases h with
      | let₂ ha hbody =>
        have e : (fun ρ : Env (τ := τ) (context β) =>
            ANF.Elaboration.Direct.denoteProgram (ε := ε) (m := m)
              (ANF.Program.HasType.let₂ ha hbody) PUnit.unit
              (envToBound ρ) >>= fun v => pure (labelInject result hout v))
          = (fun ρ =>
            (fun ρ' => ANF.Elaboration.Direct.denoteAtom (ε := ε) (m := m) ha PUnit.unit
              (envToBound ρ')) ρ >>= fun ab =>
                let q := TypeModel.tensorEquiv _ _ ab
                (fun ρ' => ANF.Elaboration.Direct.denoteProgram (ε := ε) (m := m) hbody
                  PUnit.unit (envToBound ρ') >>= fun w =>
                    pure (labelInject result hout w)) ((ρ, q.1), q.2)) := by
          funext ρ
          simp only [ANF.Elaboration.Direct.denoteProgram, bind_assoc]
          rfl
        rw [e]
        exact .let₂ (atom_denotes ha (ANF.ToSSA.atom_hasType ha))
          (ih hbody hout (ANF.ToSSA.program_hasType hbody hout))

end Semantics

end SSABridge

/-! ## The Brookes fragment -/

namespace BrookesModel

open Isotope.Elgot
open Isotope.Elgot.Brookes
open Isotope.LambdaIter (Ctx)
open Isotope.LambdaIter.LocallyNameless (Tm BoundCtx)
open Isotope.LambdaIter.Subtyping.LocallyNameless
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Translation
open Isotope.LambdaSSA.LocallyNameless.ToDeBruijn (context)

universe u

variable {Loc Val : Type u}

/-! ### The coercion-free derivation of a compilable term

`Compilable` is indexed by a derivation of the proof-relevant *subtyping*
judgment, while the SSA frontend consumes the exact, coercion-free one.  No
compilable derivation uses `sub`, so the translation is total. -/

/-- The coercion-free derivation underlying a compilable one. -/
def exactDeriv : {n : Nat} → {β : BoundCtx (MemTy Loc Val) n} →
    {t : Tm Empty (CInstr Loc Val) n} →
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit} →
    Compilable h →
      LambdaIter.LocallyNameless.HasType (CInstr Loc Val)
        (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit
  | _, _, _, _, .skip => .op (f := CInstr.skip) .unit
  | _, _, _, _, .assign l e => .op (f := CInstr.assign l e) .unit
  | _, _, _, _, .seq ca cb =>
      .let₁ (A := LambdaIter.unit) (B := LambdaIter.unit) (exactDeriv ca) (exactDeriv cb)
  | _, _, _, _, .ite b cl cr =>
      .case (A := LambdaIter.unit) (B := LambdaIter.unit) (C := LambdaIter.unit)
        (.op (f := CInstr.test b) .unit) (exactDeriv cl) (exactDeriv cr)
  | _, _, _, _, .wh b cb =>
      .iter (A := LambdaIter.unit) (B := LambdaIter.unit) .unit
        (.case (A := LambdaIter.unit) (B := LambdaIter.unit)
          (C := LambdaIter.coprod LambdaIter.unit LambdaIter.unit)
          (.op (f := CInstr.test b) .unit)
          (.let₁ (A := LambdaIter.unit)
            (B := LambdaIter.coprod LambdaIter.unit LambdaIter.unit)
            (exactDeriv cb) (.inr (A := LambdaIter.unit) .unit))
          (.inl (B := LambdaIter.unit) .unit))

/-- Embedding the coercion-free derivation recovers the original: the compilable
fragment uses no subtyping. -/
theorem toGeneric_exactDeriv : {n : Nat} → {β : BoundCtx (MemTy Loc Val) n} →
    {t : Tm Empty (CInstr Loc Val) n} →
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit} →
    (c : Compilable h) → (exactDeriv c).toGeneric = h := by
  intro n β t h c
  induction c with
  | skip => rfl
  | assign l e => rfl
  | seq ca cb iha ihb =>
      simp only [exactDeriv, LambdaIter.LocallyNameless.HasType.toGeneric, iha, ihb]
  | ite b cl cr ihl ihr =>
      simp only [exactDeriv, LambdaIter.LocallyNameless.HasType.toGeneric, ihl, ihr]
  | wh b cb ihb =>
      simp only [exactDeriv, LambdaIter.LocallyNameless.HasType.toGeneric, ihb]

/-! ### The typing leg -/

/-- Every compilable term compiles to a well-typed SSA region. -/
theorem compile_region_hasType {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    {t : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    (c : Compilable h) {L : LambdaSSA.LCtx (MemTy Loc Val)} {result : Nat}
    (hout : LambdaSSA.At L result (LambdaIter.unit : MemTy Loc Val)) :
    LambdaSSA.Region.HasType (context β) (Compile.compile result t) L :=
  Compile.compile_hasType (exactDeriv c) hout

/-- A closed compilable term compiles to a region over the empty variable
context returning to the sole label `unit`. -/
theorem compileClosed_region_hasType {t : Tm Empty (CInstr Loc Val) 0}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) .nil t LambdaIter.unit}
    (c : Compilable h) :
    LambdaSSA.Region.HasType [] (Compile.compile 0 t)
      [(LambdaIter.unit : MemTy Loc Val)] :=
  Compile.compileClosed_hasType (exactDeriv c)

/-! ### The ANF leg -/

section ANF

variable [DecidableEq Loc] [DecidableEq Val]

/-- The direct denotation of the ANF program elaborated from a compilable
derivation. -/
def anfDen {n : Nat} {β : BoundCtx (MemTy Loc Val) n} {t : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    (c : Compilable h) (ρ : BoundDen β) :
    SeqCst.Comp Loc Val (TyDen (LambdaIter.unit : MemTy Loc Val)) :=
  ANF.Elaboration.Direct.denoteProgram (ε := Eff) (m := SeqCst.Comp Loc Val)
    (ANF.Elaboration.elaborate_hasType (exactDeriv c)) PUnit.unit ρ

/-- **Preservation through ANF.**  Administrative elaboration commutes with
compilation into Brookes's language: the elaborated program's direct denotation
is the trace denotation of the compiled command. -/
theorem anfDen_eq_den_compile {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    {t : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    (c : Compilable h) (ρ : BoundDen β) :
    anfDen c ρ = SeqCst.den (compile c) := by
  rw [anfDen, ANF.Elaboration.Direct.denote_elaborate, toGeneric_exactDeriv,
    den_compile c ρ]

/-- The ANF denotation decides the operational input-output relation of the
compiled command. -/
theorem opObs_anfDen {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    {t : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    (c : Compilable h) (ρ : BoundDen β) (μ σ : SeqCst.Store Loc Val) :
    SeqCst.Op.opObs (compile c) μ σ ↔ SeqCst.obs (anfDen c ρ) μ σ := by
  rw [anfDen_eq_den_compile c ρ]
  exact (SeqCst.Op.obs_iff_opObs (compile c) μ σ).symm

/- `Fintype Loc` appears only in the completeness half inherited from
`SeqCst.fullAbstraction`. -/
set_option linter.unusedFintypeInType false

/-- Full abstraction transfers to the ANF intermediate representation: trace
inclusion of elaborated ANF programs is exactly the operational contextual
preorder of the commands they compile to, in the full concurrent language. -/
theorem anf_fullAbstraction [Fintype Loc] {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    {t t' : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    {h' : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t' LambdaIter.unit}
    (c : Compilable h) (c' : Compilable h') (ρ : BoundDen β) :
    anfDen c ρ ≤ anfDen c' ρ ↔ SeqCst.Op.OpCtxLe (compile c) (compile c') := by
  rw [anfDen_eq_den_compile c ρ, anfDen_eq_den_compile c' ρ,
    ← SeqCst.Op.opDen_eq_den (compile c), ← SeqCst.Op.opDen_eq_den (compile c')]
  exact SeqCst.Op.opFullAbstraction

/-- The equational form. -/
theorem anf_fullAbstraction_eq [Fintype Loc] {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    {t t' : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    {h' : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t' LambdaIter.unit}
    (c : Compilable h) (c' : Compilable h') (ρ : BoundDen β) :
    anfDen c ρ = anfDen c' ρ ↔ SeqCst.Op.OpCtxEq (compile c) (compile c') := by
  rw [anfDen_eq_den_compile c ρ, anfDen_eq_den_compile c' ρ,
    ← SeqCst.Op.opDen_eq_den (compile c), ← SeqCst.Op.opDen_eq_den (compile c')]
  exact SeqCst.Op.opFullAbstraction_eq

end ANF

/-! ### The SSA leg, for the loop-free fragment -/

/-- The compilable derivations that emit no control-flow graph: `skip`, `assign`
and sequencing.  `ite` and `wh` are excluded — they are exactly the two
constructors whose compilation needs a `cfg`. -/
inductive Loopfree : {n : Nat} → {β : BoundCtx (MemTy Loc Val) n} →
    {t : Tm Empty (CInstr Loc Val) n} →
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit} →
    Compilable h → Prop
  | skip {n : Nat} {β : BoundCtx (MemTy Loc Val) n} :
      Loopfree (Compilable.skip (Loc := Loc) (Val := Val) (β := β))
  | assign {n : Nat} {β : BoundCtx (MemTy Loc Val) n} (l : Loc) (e : SeqCst.Exp Loc Val) :
      Loopfree (Compilable.assign (β := β) l e)
  | seq {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
      {a : Tm Empty (CInstr Loc Val) n} {b : Tm Empty (CInstr Loc Val) (n + 1)}
      {ha : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β a LambdaIter.unit}
      {hb : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val))
        (.snoc β LambdaIter.unit) b LambdaIter.unit}
      {ca : Compilable ha} {cb : Compilable hb} :
      Loopfree ca → Loopfree cb → Loopfree (Compilable.seq ca cb)

/-- Elaborating a loop-free compilable term lands in the CFG-free ANF
fragment. -/
theorem straight_elaborate {n : Nat} {β : BoundCtx (MemTy Loc Val) n}
    {t : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    {c : Compilable h} (lf : Loopfree c) :
    SSABridge.Straight (ANF.Elaboration.elaborate t) := by
  induction lf with
  | skip =>
      simp only [ANF.Elaboration.elaborate]
      exact SSABridge.straight_bind (.ret _) (.ret _)
  | assign l e =>
      simp only [ANF.Elaboration.elaborate]
      exact SSABridge.straight_bind (.ret _) (.ret _)
  | seq _ _ iha ihb =>
      simp only [ANF.Elaboration.elaborate]
      exact SSABridge.straight_bind iha ihb

/-- **The SSA leg, for the loop-free fragment.**  The region compiled from a
loop-free compilable term denotes the Brookes trace set of the command it
compiles to, injected at the result label.  The denotation is constant in the
environment: compilable terms never read a variable. -/
theorem loopfree_region_denotes [DecidableEq Loc] [DecidableEq Val]
    {n : Nat} {β : BoundCtx (MemTy Loc Val) n} {t : Tm Empty (CInstr Loc Val) n}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) β t LambdaIter.unit}
    {c : Compilable h} (lf : Loopfree c)
    {L : LambdaSSA.LCtx (MemTy Loc Val)} {result : Nat}
    (hout : LambdaSSA.At L result (LambdaIter.unit : MemTy Loc Val))
    (hR : LambdaSSA.Region.HasType (context β) (Compile.compile result t) L) :
    RegionDenotes (m := SeqCst.Comp Loc Val) Eff hR
      (fun _ => SeqCst.den (compile c) >>= fun a => pure (labelInject result hout a)) := by
  have e : (fun ρ : Env (τ := MemTy Loc Val) (context β) =>
      ANF.Elaboration.Direct.denoteProgram (ε := Eff) (m := SeqCst.Comp Loc Val)
        (ANF.Elaboration.elaborate_hasType (exactDeriv c)) PUnit.unit
        (SSABridge.envToBound ρ) >>= fun a => pure (labelInject result hout a))
    = (fun _ => SeqCst.den (compile c) >>= fun a => pure (labelInject result hout a)) := by
    funext ρ
    rw [show ANF.Elaboration.Direct.denoteProgram (ε := Eff) (m := SeqCst.Comp Loc Val)
        (ANF.Elaboration.elaborate_hasType (exactDeriv c)) PUnit.unit
        (SSABridge.envToBound ρ)
      = anfDen c (SSABridge.envToBound ρ) from rfl, anfDen_eq_den_compile]
    rfl
  rw [← e]
  exact SSABridge.straight_denotes (straight_elaborate lf)
    (ANF.Elaboration.elaborate_hasType (exactDeriv c)) hout hR

/-- The closed case: the region compiled from a closed loop-free term, over the
empty variable context and the single label `unit`. -/
theorem loopfreeClosed_region_denotes [DecidableEq Loc] [DecidableEq Val]
    {t : Tm Empty (CInstr Loc Val) 0}
    {h : HasType (CInstr Loc Val) (.nil : Ctx Empty (MemTy Loc Val)) .nil t LambdaIter.unit}
    {c : Compilable h} (lf : Loopfree c)
    (hout : LambdaSSA.At [(LambdaIter.unit : MemTy Loc Val)] 0
      (LambdaIter.unit : MemTy Loc Val)) :
    RegionDenotes (m := SeqCst.Comp Loc Val) Eff (compileClosed_region_hasType c)
      (fun _ => SeqCst.den (compile c) >>= fun a => pure (labelInject 0 hout a)) :=
  loopfree_region_denotes lf hout (compileClosed_region_hasType c)

end BrookesModel

end Isotope.LambdaIter.Subtyping.Semantics
