import Isotope.LambdaIter.Models.Monadic.Push
import Isotope.LambdaIter.Models.Monadic.Examples
import Isotope.Elgot.Morphism.Nondet
import Isotope.Elgot.Morphism.Examples
import Isotope.Elgot.Brookes
import Isotope.Elgot.RA
import Isotope.Elgot.WS
import Isotope.Elgot.Transformer
import Isotope.Elgot.TraceSet

/-!
# Concrete algebras of lambda-iter, and morphisms between them

Over the empty signature the semantic input to `Alg.ofModel` is pure type
data: `freeInterp` interprets the freely generated universe by the evident
sets, and there are no instructions to denote.  So **every** complete Elgot
monad in the repository gives an algebra of the lambda-iter presentation, by
one uniform construction `freeAlg`.

This file instantiates it at ten monads and connects four of them by
morphisms.

## Why the morphisms are definitionally typed

`Alg.homOfReinterpret` produces a morphism into `Alg.ofModel` of a
*reinterpretation* of the source model, not into a separately-defined
algebra.  Over the empty signature `(freeModel m).reinterpret (fun f => f.elim)`
**is** `freeModel n` — same type interpretation, same (absent) instruction
denotations, and the purity coherence field is a proposition.  So `freeAlgHom`
lands in `freeAlg n` on the nose, with no transport, and the morphisms
compose and can be compared directly.

## Parallel morphisms that differ

`freeAlgHom (Transformer.Reader.evalHom r)` is a morphism
`freeAlg (ReaderT R m) ⟶ freeAlg m` for each environment `r`.  Different
environments give *different* morphisms with the *same* source and target
(`readerEvalAlgHom_ne`), so the hom-sets of `Alg Sig.empty` are not
subsingletons.

## Honest boundary

`Syn S : Alg.{u, u} S`, so the initiality statement of `Models/Initial.lean`
quantifies over algebras whose carrier lands in the same universe as the
signature.  Every algebra here is `Alg.{0, 0} Sig.empty.{0}` and so is in
scope.  A monad living one universe up — `Tree E`, whose carrier is
`Type (u+1)` — would give a perfectly good algebra but is outside the
statement as written; no such instance is claimed here.
-/

namespace Isotope.LambdaIter.Monadic

open LocallyNameless
open Isotope.Elgot
open Isotope.Elgot.RA
open CategoryTheory
open Isotope.LambdaIter.Monadic.SeqModel

/-! ### The uniform model of the empty signature -/

/-- **The free model of the empty signature in an arbitrary monad.**  The type
universe is interpreted by the evident sets; there are no instructions to
interpret, so no further data is needed and no hypothesis on `m` beyond
`Monad`. -/
def freeModel (m : Type → Type) [Monad m] : Model.{0, 0} Sig.empty.{0} m where
  interp := freeInterp
  denoteInstr f := f.elim
  denotePureInstr f := f.elim
  denoteInstr_pure f := f.elim
  tensorEquiv _ _ := Equiv.refl _
  unitEquiv := Equiv.refl _
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := Equiv.refl _

/-- The partiality model of `Models/Monadic/Free.lean` is the free model at
`Part`. -/
theorem partModel_eq_freeModel : partModel = freeModel Part := rfl

section

variable (m n : Type → Type) [Monad m] [LawfulMonad m] [Iterate m]
  [LawfulElgotMonad m]

/-- **The algebra of lambda-iter carried by a complete Elgot monad**, over the
empty signature. -/
def freeAlg : Alg.{0, 0} Sig.empty.{0} := Alg.ofModel (freeModel m)

@[simp] theorem freeAlg_denote {k : Nat} {β : BoundCtx Sig.empty.{0}.Ty k}
    {t : Tm Empty Sig.empty.{0}.Instr k} {A : Sig.empty.{0}.Ty}
    (h : HasType Sig.empty.{0}.Instr Ctx.nil β t A) :
    (freeAlg m).denote h = denote (freeModel m) h := ofModel_denote _ h

end

/-! ### The ten instances -/

/-- Partiality: deterministic, divergence-sensitive. -/
noncomputable def partAlg : Alg.{0, 0} Sig.empty.{0} := freeAlg Part

/-- Unbounded nondeterminism, angelically. -/
def setAlg : Alg.{0, 0} Sig.empty.{0} := freeAlg SetM

/-- Countable nondeterminism. -/
def csetAlg : Alg.{0, 0} Sig.empty.{0} := freeAlg Nondet.CSet

/-- Deterministic finite traces over an alphabet. -/
noncomputable def traceAlg (Sigma : Type) : Alg.{0, 0} Sig.empty.{0} :=
  freeAlg (FiniteTrace Sigma)

/-- Nondeterministic trace sets. -/
def traceSetAlg (Sigma Tau : Type) [MulAction (FreeMonoid Sigma) Tau] :
    Alg.{0, 0} Sig.empty.{0} := freeAlg (TraceSet (FreeMonoid Sigma) Tau)

/-- Brookes-style transition traces at the sequentially consistent rewriting. -/
def brookesAlg (St : Type) : Alg.{0, 0} Sig.empty.{0} :=
  freeAlg (Brookes (Brookes.SeqCst.rewriting St))

/-- The Dvir release/acquire trace monad at the `𝔠` rule set. -/
def raAlg (Loc Val : Type) : Alg.{0, 0} Sig.empty.{0} := freeAlg (Comp cRules Loc Val)

/-- The monoid-generic partial-correctness state monad. -/
def wsAlg (St W : Type) [Monoid W] : Alg.{0, 0} Sig.empty.{0} := freeAlg (WS St W)

/-- A transformer stack: state over partiality. -/
noncomputable def stateAlg (St : Type) : Alg.{0, 0} Sig.empty.{0} :=
  freeAlg (StateT St Part)

/-- A transformer stack: writer over partiality. -/
noncomputable def writerAlg (W : Type) [Monoid W] : Alg.{0, 0} Sig.empty.{0} :=
  freeAlg (WriterT W Part)

/-- A transformer stack: reader over a base monad. -/
def readerAlg (R : Type) (m : Type → Type) [Monad m] [LawfulMonad m] [Iterate m]
    [LawfulElgotMonad m] : Alg.{0, 0} Sig.empty.{0} := freeAlg (ReaderT R m)

/-! ### Morphisms -/

section Hom

variable {m n p : Type → Type}
variable [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
variable [Monad n] [LawfulMonad n] [Iterate n] [LawfulElgotMonad n]

/-- **An Elgot morphism of monads is a morphism of the corresponding
algebras.**  No transport appears: over the empty signature the
reinterpretation of `freeModel m` in `n` *is* `freeModel n`. -/
def freeAlgHom (φ : ElgotHom m n) : freeAlg m ⟶ freeAlg n :=
  Alg.homOfReinterpret (freeModel m) φ (fun f => f.elim) (fun f _ _ => f.elim)
    (fun f => f.elim)

omit [LawfulMonad m] [Iterate m] [LawfulElgotMonad m] [LawfulMonad n] [Iterate n]
  [LawfulElgotMonad n] in
/-- Transporting an environment between two free models composes, since it is
the identity on every slot. -/
theorem ofReinterpret_free_comp {q : Type → Type} [Monad q] :
    ∀ {k : Nat} {β : BoundCtx Sig.empty.{0}.Ty k} (ρ : (freeModel q).Env β),
      Env.ofReinterpret (n := n) (freeModel m) (fun f => f.elim) (fun f _ _ => f.elim)
          (Env.ofReinterpret (n := q) (freeModel n) (fun f => f.elim)
            (fun f _ _ => f.elim) ρ)
        = Env.ofReinterpret (n := q) (freeModel m) (fun f => f.elim)
            (fun f _ _ => f.elim) ρ
  | _, .nil, _ => rfl
  | _, .snoc β A, ρ => by
      apply Prod.ext
      · exact ofReinterpret_free_comp ρ.1
      · rfl

omit [LawfulMonad m] [Iterate m] [LawfulElgotMonad m] in
/-- Transporting an environment between a free model and itself is the
identity. -/
theorem ofReinterpret_free_id :
    ∀ {k : Nat} {β : BoundCtx Sig.empty.{0}.Ty k} (ρ : (freeModel m).Env β),
      Env.ofReinterpret (n := m) (freeModel m) (fun f => f.elim)
        (fun f _ _ => f.elim) ρ = ρ
  | _, .nil, _ => rfl
  | _, .snoc β A, ρ => by
      apply Prod.ext
      · exact ofReinterpret_free_id ρ.1
      · rfl

@[simp] theorem freeAlgHom_map (φ : ElgotHom m n) {k : Nat}
    {β : BoundCtx Sig.empty.{0}.Ty k} {A : Sig.empty.{0}.Ty}
    (x : (freeAlg m).El β A) :
    (freeAlgHom φ).map x =
      fun ρ => φ.app (x (Env.ofReinterpret (freeModel m) _ _ ρ)) := rfl

/-- On a closed term the induced map is simply `φ` applied to the denotation:
the empty environment needs no transport. -/
@[simp] theorem freeAlgHom_map_nil (φ : ElgotHom m n)
    {A : Sig.empty.{0}.Ty} (x : (freeAlg m).El BoundCtx.nil A) :
    (freeAlgHom φ).map x PUnit.unit = φ.app (x PUnit.unit) := rfl

/-- The induced map sends a denotation to the denotation in the target, which
is the content of `Alg.Hom.map_denote` here. -/
theorem freeAlgHom_denote (φ : ElgotHom m n) {A : Sig.empty.{0}.Ty}
    {t : Tm Empty Sig.empty.{0}.Instr 0}
    (h : HasType Sig.empty.{0}.Instr Ctx.nil BoundCtx.nil t A) :
    φ.app (denote (freeModel m) h PUnit.unit) =
      denote (freeModel n) h PUnit.unit := by
  have := congrFun ((freeAlgHom φ).map_denote h) PUnit.unit
  rw [freeAlgHom_map] at this
  rw [← freeAlg_denote m h, ← freeAlg_denote n h]
  exact this

/-- **`freeAlgHom` is functorial**: it takes the identity Elgot morphism to the
identity morphism of algebras. -/
theorem freeAlgHom_id : freeAlgHom (ElgotHom.id m) = CategoryTheory.CategoryStruct.id (freeAlg m) := by
  apply Alg.Hom.ext
  intro k β A x
  funext ρ
  show x _ = x ρ
  rw [ofReinterpret_free_id]

variable [Monad p] [LawfulMonad p] [Iterate p] [LawfulElgotMonad p]

/-- **`freeAlgHom` is functorial**: it takes composition to composition. -/
theorem freeAlgHom_comp (φ : ElgotHom m n) (ψ : ElgotHom n p) :
    freeAlgHom φ ≫ freeAlgHom ψ = freeAlgHom (φ.comp ψ) := by
  apply Alg.Hom.ext
  intro k β A x
  funext ρ
  show ψ.app (φ.app (x _)) = ψ.app (φ.app (x _))
  rw [ofReinterpret_free_comp (m := m) (n := n) (q := p) ρ]

end Hom

/-! ### The named morphisms -/

/-- **The author's example: the graph map `Part → Set` as a morphism of
algebras.**  A partial computation is read as the nondeterministic
computation with the same (at most one) possible result. -/
noncomputable def partToSetAlgHom : partAlg ⟶ setAlg := freeAlgHom Part.toSetHom

/-- Partiality lands in countable nondeterminism. -/
noncomputable def partToCSetAlgHom : partAlg ⟶ csetAlg := freeAlgHom Part.toCSetHom

/-- Forgetting countability. -/
def csetToSetAlgHom : csetAlg ⟶ setAlg := freeAlgHom CSet.toSetHom

/-- The deterministic trace algebra inside the nondeterministic one. -/
noncomputable def traceToTraceSetAlgHom (Sigma Tau : Type)
    [MulAction (FreeMonoid Sigma) Tau] : traceAlg Sigma ⟶ traceSetAlg Sigma Tau :=
  freeAlgHom FiniteTrace.toTraceSetHom

/-- **The comparison triangle commutes**, as morphisms of algebras. -/
theorem partToCSet_comp_csetToSet :
    partToCSetAlgHom ≫ csetToSetAlgHom = partToSetAlgHom := by
  apply Alg.Hom.ext
  intro k β A x
  funext ρ
  show CSet.toSetHom.app (Part.toCSetHom.app (x _)) = Part.toSetHom.app (x _)
  rw [ofReinterpret_free_comp (m := Part) (n := Nondet.CSet) (q := SetM) ρ]
  rfl

/-- Evaluating a reader computation at a fixed environment, as a morphism of
algebras. -/
def readerEvalAlgHom {R : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Iterate m] [LawfulElgotMonad m] (r : R) : readerAlg R m ⟶ freeAlg m :=
  freeAlgHom (Transformer.Reader.evalHom r)

/-- A carrier element of the reader algebra that distinguishes environments:
the boolean it returns is the one it reads. -/
noncomputable def oracle : (readerAlg Bool Part).El BoundCtx.nil EmptyTy.boolTy :=
  fun _ r => pure (cond r (Sum.inl ()) (Sum.inr ()))

/-- **A parallel pair of morphisms of algebras that differ.**  Reading the
environment at two distinct values gives two morphisms
`readerAlg Bool Part ⟶ partAlg` with the same source and target; they
disagree already on a closed carrier element of boolean type.  So the
hom-sets of `Alg Sig.empty` are not subsingletons, and the category of models
has genuine content. -/
theorem readerEvalAlgHom_ne :
    readerEvalAlgHom (R := Bool) (m := Part) true ≠ readerEvalAlgHom false := by
  intro h
  have h2 : (Part.some (Sum.inl ()) : Part (Unit ⊕ Unit)) = Part.some (Sum.inr ()) :=
    congrFun (congrArg (fun F => Alg.Hom.map F oracle) h) PUnit.unit
  exact Sum.inl_ne_inr (_root_.Part.some_inj.mp h2)

end Isotope.LambdaIter.Monadic

