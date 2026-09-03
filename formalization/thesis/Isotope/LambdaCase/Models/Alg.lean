import Isotope.LambdaIter.Signature.Category
import Isotope.LambdaCase.Equiv

/-!
# Models of lambda-case as algebras of its equational presentation

A model of a signature `S` is an *algebra of the presented equational theory*
of lambda-case: one operation per term former, an interpretation of typing
derivations built from them, and two propositional obligations — coherence in
the derivation and soundness for `Equiv`.

This is the exact analogue of `Isotope.LambdaIter.Alg`, with the `iter`
operation and its preservation law deleted, since lambda-case is the
iteration-free fragment.  The signature itself is *reused verbatim*: a
lambda-case signature is an `Isotope.LambdaIter.Sig`, because the parameters of
`LambdaCase.LocallyNameless.HasType` and `.Equiv` are exactly the components of
that structure.  Sharing `Sig` is what lets the comparison theorems between the
three calculi be stated over a single object.

The carrier type `Alg.Ops.El` is indexed by lambda-case bound contexts and
lambda-case types, and `Ops.denote` recurses on `LambdaCase.…HasType`, so this
is genuinely a different structure from `LambdaIter.Alg`; only `Sig` is shared.

## Why this notion of model, and what it does not say

The categorical interface in `Isotope/LambdaCase/Semantics/Categorical.lean`
factors comparable data through a distributive Freyd category, but the two
coherence classes it would need (`TypingCoherent` and `LawfulModel`, in the
lambda-iter namespace) are instantiated only at the Kleisli category of a
lawful Elgot monad (`Isotope/LambdaIter/Semantics/Kleisli/Model.lean`), and no
lambda-case algebra is built from them here.
Making coherence and soundness *fields* of the model structure, rather than
global classes, is what makes a category of models and a statement of
initiality possible at all.  The price, stated plainly:

* **A model in this sense is an algebra of the presentation, not a Freyd
  category.**  Nothing here proves that any monad or any Freyd category gives
  such an algebra; that would require discharging `coh` and `sound` in the
  model, which is exactly the work those two missing instances represent.
* In particular there is no soundness theorem anywhere in this repository
  saying that the monadic or categorical denotation of lambda-case respects
  `Equiv`, so no such denotation is known to be an object of `Alg S`.
* The only algebras constructed in this development are the syntactic one and
  the ones in `Isotope/LambdaCase/Models/Limits.lean` and
  `Isotope/LambdaCase/Models/Examples.lean`.

## Fixed syntax parameters

Free variables are fixed at `ν := Empty` and the free context at `LambdaIter.Ctx.nil`, so
a model interprets terms in the bound context alone.  This matches
`Isotope.LambdaIter.Alg` and is what lets the comparison functors of
`Isotope/LambdaCase/Models/Comparison.lean` be stated.
-/

namespace Isotope.LambdaCase

open LocallyNameless

open Isotope.LambdaIter (Sig instrSrc instrTrg)

universe u w w'

namespace Alg

/-- The operations of a model: one per term former of lambda-case, indexed by
the bound context and result type they act at.

The carrier is called `El` (not `Hom`) so that `Alg.Hom` may name the
morphisms of models. -/
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
  /-- The unit value. -/
  unit : ∀ {n : Nat} {β : BoundCtx S.Ty n}, El β LambdaIter.TypeFormers.unit
  /-- Pairing. -/
  pair : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty},
    El β A → El β B → El β (LambdaIter.TypeFormers.tensor A B)
  /-- Pattern-matching a pair. -/
  let₂ : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty},
    El β (LambdaIter.TypeFormers.tensor A B) → El ((β.snoc A).snoc B) C → El β C
  /-- Left injection. -/
  inl : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty},
    El β A → El β (LambdaIter.TypeFormers.coprod A B)
  /-- Right injection. -/
  inr : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty},
    El β B → El β (LambdaIter.TypeFormers.coprod A B)
  /-- Case analysis. -/
  case : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty},
    El β (LambdaIter.TypeFormers.coprod A B) → El (β.snoc A) C → El (β.snoc B) C →
      El β C
  /-- Elimination of the empty type. -/
  abort : ∀ {n : Nat} {β : BoundCtx S.Ty n} {C : S.Ty},
    El β LambdaIter.TypeFormers.empty → El β C

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
  | _, _, _, _, .unit => X.unit
  | _, _, _, _, .pair ha hb => X.pair (X.denote ha) (X.denote hb)
  | _, _, _, _, .let₂ ha hc => X.let₂ (X.denote ha) (X.denote hc)
  | _, _, _, _, .inl ha => X.inl (X.denote ha)
  | _, _, _, _, .inr hb => X.inr (X.denote hb)
  | _, _, _, _, .case he hl hr => X.case (X.denote he) (X.denote hl) (X.denote hr)
  | _, _, _, _, .abort ha => X.abort (X.denote ha)

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

@[simp] theorem Ops.denote_unit {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} :
    X.denote (β := β) (t := .unit) .unit = X.unit := rfl

@[simp] theorem Ops.denote_pair {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} {a b : Tm Empty S.Instr n}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a A)
    (hb : HasType S.Instr LambdaIter.Ctx.nil β b B) :
    X.denote (.pair ha hb) = X.pair (X.denote ha) (X.denote hb) := rfl

@[simp] theorem Ops.denote_let₂ {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty} {a : Tm Empty S.Instr n}
    {c : Tm Empty S.Instr (n + 2)}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a (LambdaIter.TypeFormers.tensor A B))
    (hc : HasType S.Instr LambdaIter.Ctx.nil ((β.snoc A).snoc B) c C) :
    X.denote (.let₂ ha hc) = X.let₂ (X.denote ha) (X.denote hc) := rfl

@[simp] theorem Ops.denote_inl {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a A) :
    X.denote (HasType.inl (B := B) ha) = X.inl (B := B) (X.denote ha) := rfl

@[simp] theorem Ops.denote_inr {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} {b : Tm Empty S.Instr n}
    (hb : HasType S.Instr LambdaIter.Ctx.nil β b B) :
    X.denote (HasType.inr (A := A) hb) = X.inr (A := A) (X.denote hb) := rfl

@[simp] theorem Ops.denote_case {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty} {e : Tm Empty S.Instr n}
    {l r : Tm Empty S.Instr (n + 1)}
    (he : HasType S.Instr LambdaIter.Ctx.nil β e (LambdaIter.TypeFormers.coprod A B))
    (hl : HasType S.Instr LambdaIter.Ctx.nil (β.snoc A) l C)
    (hr : HasType S.Instr LambdaIter.Ctx.nil (β.snoc B) r C) :
    X.denote (.case he hl hr) = X.case (X.denote he) (X.denote hl) (X.denote hr) :=
  rfl

@[simp] theorem Ops.denote_abort {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {C : S.Ty} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr LambdaIter.Ctx.nil β a LambdaIter.TypeFormers.empty) :
    X.denote (HasType.abort (C := C) ha) = X.abort (C := C) (X.denote ha) := rfl

end Alg

/-- A model of the signature `S`: operations for every term former of
lambda-case, coherent in the typing derivation and sound for the equational
theory `Equiv`.

`coh` and `sound` are *fields*, not global class instances.  That is the whole
design: it makes `Alg S` a class of objects that can be organized into a
category, at the cost that inhabiting it requires proving both. -/
structure Alg (S : Sig.{u}) extends Alg.Ops.{u, w} S where
  /-- The denotation depends only on the term and its type, not on the chosen
  typing derivation. -/
  coh : ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h k : HasType S.Instr LambdaIter.Ctx.nil β t A), toOps.denote h = toOps.denote k
  /-- Equal terms have equal denotations. -/
  sound : ∀ {n : Nat} {β : BoundCtx S.Ty n} {a b : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β a A) (k : HasType S.Instr LambdaIter.Ctx.nil β b A),
    Equiv (Φ := S.Instr) S.pureEff LambdaIter.Ctx.nil β a b A → toOps.denote h = toOps.denote k

namespace Alg

variable {S : Sig.{u}}

/-- The interpretation of a typing derivation in a model. -/
abbrev denote (X : Alg.{u, w} S) {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) : X.El β A := X.toOps.denote h

/-- A morphism of models: a map of carriers commuting with all ten non-variable
term formers, and with variables. -/
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
  /-- The unit value is preserved. -/
  map_unit : ∀ {n : Nat} {β : BoundCtx S.Ty n},
    map (X.unit (β := β)) = Y.unit
  /-- Pairing is preserved. -/
  map_pair : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    (a : X.El β A) (b : X.El β B), map (X.pair a b) = Y.pair (map a) (map b)
  /-- Pair elimination is preserved. -/
  map_let₂ : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty}
    (a : X.El β (LambdaIter.TypeFormers.tensor A B))
    (c : X.El ((β.snoc A).snoc B) C),
    map (X.let₂ a c) = Y.let₂ (map a) (map c)
  /-- Left injection is preserved. -/
  map_inl : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} (a : X.El β A),
    map (X.inl (B := B) a) = Y.inl (B := B) (map a)
  /-- Right injection is preserved. -/
  map_inr : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} (b : X.El β B),
    map (X.inr (A := A) b) = Y.inr (A := A) (map b)
  /-- Case analysis is preserved. -/
  map_case : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty}
    (e : X.El β (LambdaIter.TypeFormers.coprod A B)) (l : X.El (β.snoc A) C)
    (r : X.El (β.snoc B) C),
    map (X.case e l r) = Y.case (map e) (map l) (map r)
  /-- Empty elimination is preserved. -/
  map_abort : ∀ {n : Nat} {β : BoundCtx S.Ty n} {C : S.Ty}
    (a : X.El β LambdaIter.TypeFormers.empty),
    map (X.abort (C := C) a) = Y.abort (C := C) (map a)

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
  map_unit := rfl
  map_pair _ _ := rfl
  map_let₂ _ _ := rfl
  map_inl _ := rfl
  map_inr _ := rfl
  map_case _ _ _ := rfl
  map_abort _ := rfl

@[simp] theorem id_map (X : Alg.{u, w} S) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} (x : X.El β A) : (Hom.id X).map x = x := rfl

/-- Composition of model morphisms. -/
def comp (F : Hom X Y) (G : Hom Y Z) : Hom X Z where
  map x := G.map (F.map x)
  map_var i := by rw [F.map_var, G.map_var]
  map_op f a := by rw [F.map_op, G.map_op]
  map_let₁ a b := by rw [F.map_let₁, G.map_let₁]
  map_unit := by intro n β; rw [F.map_unit, G.map_unit]
  map_pair a b := by rw [F.map_pair, G.map_pair]
  map_let₂ a c := by rw [F.map_let₂, G.map_let₂]
  map_inl a := by rw [F.map_inl, G.map_inl]
  map_inr b := by rw [F.map_inr, G.map_inr]
  map_case e l r := by rw [F.map_case, G.map_case]
  map_abort a := by rw [F.map_abort, G.map_abort]

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
This is the fact that makes the model category relevant to initiality: a
morphism out of the syntactic model is determined, since `map` of a denotation
is again a denotation. -/
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
  | _, _, _, _, .unit => F.map_unit
  | _, _, _, _, .pair ha hb => by
      rw [Ops.denote_pair, Ops.denote_pair, F.map_pair, F.map_denote ha,
        F.map_denote hb]
  | _, _, _, _, .let₂ ha hc => by
      rw [Ops.denote_let₂, Ops.denote_let₂, F.map_let₂, F.map_denote ha,
        F.map_denote hc]
  | _, _, _, _, .inl ha => by
      rw [Ops.denote_inl, Ops.denote_inl, F.map_inl, F.map_denote ha]
  | _, _, _, _, .inr hb => by
      rw [Ops.denote_inr, Ops.denote_inr, F.map_inr, F.map_denote hb]
  | _, _, _, _, .case he hl hr => by
      rw [Ops.denote_case, Ops.denote_case, F.map_case, F.map_denote he,
        F.map_denote hl, F.map_denote hr]
  | _, _, _, _, .abort ha => by
      rw [Ops.denote_abort, Ops.denote_abort, F.map_abort, F.map_denote ha]

/-- A model morphism commutes with the interpretation of typing derivations. -/
@[simp] theorem Hom.map_denote' {X Y : Alg.{u, w} S} (F : Hom X Y)
    {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr LambdaIter.Ctx.nil β t A) :
    F.map (X.denote h) = Y.denote h := F.map_denote h

end Alg

end Isotope.LambdaCase
