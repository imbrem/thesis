import Isotope.LambdaIter.Signature.Category
import Isotope.LambdaSeq.Equiv

/-!
# Models of lambda-seq as algebras of its equational presentation

A model of a signature `S` is an *algebra of the presented equational theory*
of lambda-seq: one operation per term former, an interpretation of typing
derivations built from them, and two propositional obligations — coherence in
the derivation and soundness for `Equiv`.

Lambda-seq is the smallest of the three calculi: three term formers (`var`,
`op`, `let₁`) and four axioms, with no unit, tensor, coproduct, empty type or
iteration.  So an algebra has three operations and a morphism three laws.

The signature is *reused verbatim* from lambda-iter: a lambda-seq signature is
an `Isotope.LambdaIter.Sig`.  Its type formers play no role in the lambda-seq
judgments, but sharing the structure is what lets the comparison theorems
between the three calculi be stated over a single object.

## Why this notion of model, and what it does not say

The categorical interface in `Isotope/LambdaSeq/Categorical.lean` interprets
lambda-seq in a Freyd category, but there is **no theorem anywhere in this
repository saying that any lambda-seq denotation respects `Equiv`**, and no
lawfulness class with an instance.  Making coherence and soundness *fields* of
the model structure, rather than global classes, is what makes a category of
models and a statement of initiality possible at all.  The price:

* **A model in this sense is an algebra of the presentation, not a Freyd
  category.**  Nothing here proves that a monad or a Freyd category gives such
  an algebra; that would mean discharging `coh` and `sound`.
* The only algebras constructed in this development are the syntactic one and
  the ones in `Models/Limits.lean` and `Models/Examples.lean`.

## Fixed syntax parameters

Free variables are fixed at `ν := Empty` and the free context at `Ctx.nil`, so
a model interprets terms in the bound context alone.  This matches
`Isotope.LambdaIter.Alg` and `Isotope.LambdaCase.Alg`.
-/

namespace Isotope.LambdaSeq

open LocallyNameless

open Isotope.LambdaIter (Sig instrSrc instrTrg)

universe u w

namespace Alg

/-- The operations of a model: one per term former of lambda-seq, indexed by
the bound context and result type they act at. -/
structure Ops (S : Sig.{u}) : Type (max u (w + 1)) where
  /-- The carrier: denotations of terms of type `A` in bound context `β`. -/
  El : {n : Nat} → BoundCtx S.Ty n → S.Ty → Type w
  /-- Projection onto a bound variable. -/
  var : ∀ {n : Nat} {β : BoundCtx S.Ty n} (i : Fin n), El β (β.get i)
  /-- Application of a primitive instruction. -/
  op : ∀ {n : Nat} {β : BoundCtx S.Ty n} (f : S.Instr),
    El β (instrSrc f) → El β (instrTrg f)
  /-- Sequencing. -/
  let₁ : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty},
    El β A → El (β.snoc A) B → El β B

/-- The interpretation of a typing derivation in a collection of operations.
Structural recursion on the derivation; the free-variable case is impossible
because the free context is empty. -/
def Ops.denote {S : Sig.{u}} (X : Ops.{u, w} S) :
    {n : Nat} → {β : BoundCtx S.Ty n} → {t : Tm Empty S.Instr n} → {A : S.Ty} →
      HasType S.Instr LambdaIter.Ctx.nil β t A → X.El β A
  | _, _, _, _, .fv h => absurd h (by simp [LambdaIter.Ctx.lookup])
  | _, _, _, _, .bv (i := i) => X.var i
  | _, _, _, _, .op (f := f) ha => X.op f (X.denote ha)
  | _, _, _, _, .let₁ ha hb => X.let₁ (X.denote ha) (X.denote hb)

@[simp] theorem Ops.denote_bv {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} (i : Fin n) :
    X.denote (β := β) (.bv (i := i)) = X.var i := rfl

@[simp] theorem Ops.denote_op {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {f : S.Instr} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a (instrSrc f)) :
    X.denote (.op ha) = X.op f (X.denote ha) := rfl

@[simp] theorem Ops.denote_let₁ {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} {a : Tm Empty S.Instr n}
    {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a A)
    (hb : HasType S.Instr LambdaIter.Ctx.nil (β.snoc A) b B) :
    X.denote (.let₁ ha hb) = X.let₁ (X.denote ha) (X.denote hb) := rfl

end Alg

/-- A model of the signature `S`: operations for every term former of
lambda-seq, coherent in the typing derivation and sound for the equational
theory `Equiv`.

`coh` and `sound` are *fields*, not global class instances. -/
structure Alg (S : Sig.{u}) extends Alg.Ops.{u, w} S where
  /-- The denotation depends only on the term and its type, not on the chosen
  typing derivation. -/
  coh : ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h k : HasType S.Instr LambdaIter.Ctx.nil β t A),
    toOps.denote h = toOps.denote k
  /-- Equal terms have equal denotations. -/
  sound : ∀ {n : Nat} {β : BoundCtx S.Ty n} {a b : Tm Empty S.Instr n}
    {A : S.Ty} (h : HasType S.Instr LambdaIter.Ctx.nil β a A)
    (k : HasType S.Instr LambdaIter.Ctx.nil β b A),
    Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β a b A →
      toOps.denote h = toOps.denote k

namespace Alg

variable {S : Sig.{u}}

/-- The interpretation of a typing derivation in a model. -/
abbrev denote (X : Alg.{u, w} S) {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) : X.El β A := X.toOps.denote h

/-- A morphism of models: a map of carriers commuting with all three
operations. -/
structure Hom (X Y : Alg.{u, w} S) : Type (max u w) where
  /-- The underlying map of carriers. -/
  map : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}, X.El β A → Y.El β A
  /-- Variables are preserved. -/
  map_var : ∀ {n : Nat} {β : BoundCtx S.Ty n} (i : Fin n),
    map (X.var (β := β) i) = Y.var i
  /-- Instruction application is preserved. -/
  map_op : ∀ {n : Nat} {β : BoundCtx S.Ty n} (f : S.Instr)
    (a : X.El β (instrSrc f)), map (X.op f a) = Y.op f (map a)
  /-- Sequencing is preserved. -/
  map_let₁ : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    (a : X.El β A) (b : X.El (β.snoc A) B),
    map (X.let₁ a b) = Y.let₁ (map a) (map b)

namespace Hom

variable {X Y Z : Alg.{u, w} S}

/-- Two model morphisms agree as soon as their carrier maps do. -/
@[ext] theorem ext {F G : Hom X Y}
    (h : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty} (x : X.El β A),
      F.map x = G.map x) : F = G := by
  cases F; cases G
  congr 1
  funext n β A x
  exact h x

/-- The identity model morphism. -/
def id (X : Alg.{u, w} S) : Hom X X where
  map x := x
  map_var _ := rfl
  map_op _ _ := rfl
  map_let₁ _ _ := rfl

@[simp] theorem id_map (X : Alg.{u, w} S) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} (x : X.El β A) : (Hom.id X).map x = x := rfl

/-- Composition of model morphisms. -/
def comp (F : Hom X Y) (G : Hom Y Z) : Hom X Z where
  map x := G.map (F.map x)
  map_var i := by rw [F.map_var, G.map_var]
  map_op f a := by rw [F.map_op, G.map_op]
  map_let₁ a b := by rw [F.map_let₁, G.map_let₁]

@[simp] theorem comp_map (F : Hom X Y) (G : Hom Y Z) {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} (x : X.El β A) :
    (F.comp G).map x = G.map (F.map x) := rfl

end Hom

/-- Models of a fixed signature and their morphisms form a category. -/
instance instCategory (S : Sig.{u}) :
    CategoryTheory.Category.{max u w} (Alg.{u, w} S) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem category_id_map (X : Alg.{u, w} S) {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} (x : X.El β A) :
    (CategoryTheory.CategoryStruct.id X).map x = x := rfl

@[simp] theorem category_comp_map {X Y Z : Alg.{u, w} S} (F : X ⟶ Y) (G : Y ⟶ Z)
    {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty} (x : X.El β A) :
    (CategoryTheory.CategoryStruct.comp F G).map x = G.map (F.map x) := rfl

/-- A model morphism commutes with the interpretation of typing derivations.
This is the fact that makes the model category relevant to initiality. -/
theorem Hom.map_denote {X Y : Alg.{u, w} S} (F : Hom X Y) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
      (h : HasType S.Instr LambdaIter.Ctx.nil β t A),
      F.map (X.toOps.denote h) = Y.toOps.denote h
  | _, _, _, _, .fv h => absurd h (by simp [LambdaIter.Ctx.lookup])
  | _, _, _, _, .bv => F.map_var _
  | _, _, _, _, .op ha => by
      rw [Ops.denote_op, Ops.denote_op, F.map_op, F.map_denote ha]
  | _, _, _, _, .let₁ ha hb => by
      rw [Ops.denote_let₁, Ops.denote_let₁, F.map_let₁, F.map_denote ha,
        F.map_denote hb]

/-- A model morphism commutes with the interpretation of typing derivations. -/
@[simp] theorem Hom.map_denote' {X Y : Alg.{u, w} S} (F : Hom X Y)
    {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    F.map (X.denote h) = Y.denote h := F.map_denote h

end Alg

end Isotope.LambdaSeq
