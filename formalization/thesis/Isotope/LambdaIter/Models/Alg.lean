import Isotope.LambdaIter.Signature.Category
import Isotope.LambdaIter.Equiv

/-!
# Models of lambda-iter as algebras of its equational presentation

A model of a signature `S` is an *algebra of the presented equational theory*:
one operation per term former, an interpretation of typing derivations built
from them, and two propositional obligations — coherence in the derivation and
soundness for `Eqv`.

## Why this notion of model, and what it does not say

The categorical interface in `Isotope/LambdaIter/Semantics/Categorical.lean`
factors the same data through a Freyd category, through its two coherence
classes (`TypingCoherent` and `LawfulModel`).  Making them *fields* of the
model structure, rather than global classes, is what makes a category of models
and a statement of initiality possible at all.  The price, stated plainly:

* **A model in this sense is an algebra of the presentation, not a Freyd or
  Elgot category.**  Nothing *in this file* builds an algebra from a Freyd
  category; that is `Models/Categorical/Alg.lean`'s `Alg.ofCategorical`, which
  discharges `coh` and `sound` from the two coherence classes.  Those classes
  are instantiated at the Kleisli category of a lawful Elgot monad in
  `Isotope/LambdaIter/Semantics/Kleisli/Model.lean`; no instance is known for a
  general strong Elgot Freyd category.
* Every lawful Elgot *monad* with an interpretation of the signature does give
  one: `Models/Monadic/Alg.lean`'s `Alg.ofModel`.  It is instantiated at ten
  concrete monads in `Models/Monadic/Concrete.lean`, so the class of algebras
  is not exhausted by the formal constructions of `Models/Limits.lean` (a
  terminal algebra and binary products) -- it contains partiality, the
  powerset, interaction-free trace models, Brookes-style transition traces and
  the release/acquire model, together with morphisms between them.

## Fixed syntax parameters

Free variables are fixed at `ν := Empty` and the free context at `Ctx.nil`, so
a model interprets terms in the bound context alone.  Nothing is lost: `Eqv`
and `HasType` both admit free weakening (`HasType.weaken`), so every judgment
over a general free context `Γ` transports to a bound-only one by moving `Γ`'s
visible slots into `β`.
-/

namespace Isotope.LambdaIter

open LocallyNameless

universe u w w'

namespace Alg

/-- The operations of a model: one per term former of lambda-iter, indexed by
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
  unit : ∀ {n : Nat} {β : BoundCtx S.Ty n}, El β LambdaIter.unit
  /-- Pairing. -/
  pair : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty},
    El β A → El β B → El β (LambdaIter.tensor A B)
  /-- Pattern-matching a pair. -/
  let₂ : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty},
    El β (LambdaIter.tensor A B) → El ((β.snoc A).snoc B) C → El β C
  /-- Left injection. -/
  inl : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty},
    El β A → El β (LambdaIter.coprod A B)
  /-- Right injection. -/
  inr : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty},
    El β B → El β (LambdaIter.coprod A B)
  /-- Case analysis. -/
  case : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty},
    El β (LambdaIter.coprod A B) → El (β.snoc A) C → El (β.snoc B) C → El β C
  /-- Elimination of the empty type. -/
  abort : ∀ {n : Nat} {β : BoundCtx S.Ty n} {C : S.Ty},
    El β LambdaIter.empty → El β C
  /-- Iteration. -/
  iter : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty},
    El β A → El (β.snoc A) (LambdaIter.coprod B A) → El β B

/-- The interpretation of a typing derivation in a collection of operations.
Structural recursion on the derivation; the free-variable case is impossible
because the free context is empty. -/
def Ops.denote {S : Sig.{u}} (X : Ops.{u, w} S) :
    {n : Nat} → {β : BoundCtx S.Ty n} → {t : Tm Empty S.Instr n} → {A : S.Ty} →
      HasType S.Instr Ctx.nil β t A → X.El β A
  | _, _, _, _, .fv h => absurd h (by simp [Ctx.lookup])
  | _, _, _, _, .bv (ι := i) => X.var i
  | _, _, _, _, .op (f := f) ha => X.op f (X.denote ha)
  | _, _, _, _, .let₁ ha hb => X.let₁ (X.denote ha) (X.denote hb)
  | _, _, _, _, .unit => X.unit
  | _, _, _, _, .pair ha hb => X.pair (X.denote ha) (X.denote hb)
  | _, _, _, _, .let₂ ha hc => X.let₂ (X.denote ha) (X.denote hc)
  | _, _, _, _, .inl ha => X.inl (X.denote ha)
  | _, _, _, _, .inr hb => X.inr (X.denote hb)
  | _, _, _, _, .case he hl hr => X.case (X.denote he) (X.denote hl) (X.denote hr)
  | _, _, _, _, .abort ha => X.abort (X.denote ha)
  | _, _, _, _, .iter ha hb => X.iter (X.denote ha) (X.denote hb)

@[simp] theorem Ops.denote_bv {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} (i : Fin n) :
    X.denote (β := β) (.bv (ι := i)) = X.var i := rfl

@[simp] theorem Ops.denote_op {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {f : S.Instr} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a (instrSrc f)) :
    X.denote (.op ha) = X.op f (X.denote ha) := rfl

@[simp] theorem Ops.denote_let₁ {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} {a : Tm Empty S.Instr n}
    {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b B) :
    X.denote (.let₁ ha hb) = X.let₁ (X.denote ha) (X.denote hb) := rfl

@[simp] theorem Ops.denote_unit {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} :
    X.denote (β := β) (t := .unit) .unit = X.unit := rfl

@[simp] theorem Ops.denote_pair {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} {a b : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a A) (hb : HasType S.Instr Ctx.nil β b B) :
    X.denote (.pair ha hb) = X.pair (X.denote ha) (X.denote hb) := rfl

@[simp] theorem Ops.denote_let₂ {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty} {a : Tm Empty S.Instr n}
    {c : Tm Empty S.Instr (n + 2)}
    (ha : HasType S.Instr Ctx.nil β a (LambdaIter.tensor A B))
    (hc : HasType S.Instr Ctx.nil ((β.snoc A).snoc B) c C) :
    X.denote (.let₂ ha hc) = X.let₂ (X.denote ha) (X.denote hc) := rfl

@[simp] theorem Ops.denote_inl {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a A) :
    X.denote (HasType.inl (B := B) ha) = X.inl (B := B) (X.denote ha) := rfl

@[simp] theorem Ops.denote_inr {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} {b : Tm Empty S.Instr n}
    (hb : HasType S.Instr Ctx.nil β b B) :
    X.denote (HasType.inr (A := A) hb) = X.inr (A := A) (X.denote hb) := rfl

@[simp] theorem Ops.denote_case {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty} {e : Tm Empty S.Instr n}
    {l r : Tm Empty S.Instr (n + 1)}
    (he : HasType S.Instr Ctx.nil β e (LambdaIter.coprod A B))
    (hl : HasType S.Instr Ctx.nil (β.snoc A) l C)
    (hr : HasType S.Instr Ctx.nil (β.snoc B) r C) :
    X.denote (.case he hl hr) = X.case (X.denote he) (X.denote hl) (X.denote hr) := rfl

@[simp] theorem Ops.denote_abort {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {C : S.Ty} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a LambdaIter.empty) :
    X.denote (HasType.abort (C := C) ha) = X.abort (C := C) (X.denote ha) := rfl

@[simp] theorem Ops.denote_iter {S : Sig.{u}} (X : Ops.{u, w} S)
    {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} {a : Tm Empty S.Instr n}
    {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b (LambdaIter.coprod B A)) :
    X.denote (.iter ha hb) = X.iter (X.denote ha) (X.denote hb) := rfl

end Alg

/-- A model of the signature `S`: operations for every term former, coherent
in the typing derivation and sound for the equational theory `Eqv`.

`coh` and `sound` are *fields*, not global class instances.  That is the whole
design: it makes `Alg S` a class of objects that can be organized into a
category, at the cost that inhabiting it requires proving both. -/
structure Alg (S : Sig.{u}) extends Alg.Ops.{u, w} S where
  /-- The denotation depends only on the term and its type, not on the chosen
  typing derivation. -/
  coh : ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h k : HasType S.Instr Ctx.nil β t A), toOps.denote h = toOps.denote k
  /-- Equal terms have equal denotations. -/
  sound : ∀ {n : Nat} {β : BoundCtx S.Ty n} {a b : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β a A) (k : HasType S.Instr Ctx.nil β b A),
    Eqv (Φ := S.Instr) S.pureEff Ctx.nil β a b A → toOps.denote h = toOps.denote k

namespace Alg

variable {S : Sig.{u}}

/-- The interpretation of a typing derivation in a model. -/
abbrev denote (X : Alg.{u, w} S) {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) : X.El β A := X.toOps.denote h

/-- A morphism of models: a map of carriers commuting with all eleven term
formers.  (`var` accounts for the twelfth operation.) -/
structure Hom (X Y : Alg.{u, w} S) : Type (max u w) where
  /-- The underlying map of carriers. -/
  map : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}, X.El β A → Y.El β A
  /-- Variables are preserved. -/
  map_var : ∀ {n : Nat} {β : BoundCtx S.Ty n} (i : Fin n),
    map (X.var (β := β) i) = Y.var i
  /-- Instruction application is preserved. -/
  map_op : ∀ {n : Nat} {β : BoundCtx S.Ty n} (f : S.Instr) (a : X.El β (instrSrc f)),
    map (X.op f a) = Y.op f (map a)
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
    (a : X.El β (LambdaIter.tensor A B)) (c : X.El ((β.snoc A).snoc B) C),
    map (X.let₂ a c) = Y.let₂ (map a) (map c)
  /-- Left injection is preserved. -/
  map_inl : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} (a : X.El β A),
    map (X.inl (B := B) a) = Y.inl (B := B) (map a)
  /-- Right injection is preserved. -/
  map_inr : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} (b : X.El β B),
    map (X.inr (A := A) b) = Y.inr (A := A) (map b)
  /-- Case analysis is preserved. -/
  map_case : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty}
    (e : X.El β (LambdaIter.coprod A B)) (l : X.El (β.snoc A) C) (r : X.El (β.snoc B) C),
    map (X.case e l r) = Y.case (map e) (map l) (map r)
  /-- Empty elimination is preserved. -/
  map_abort : ∀ {n : Nat} {β : BoundCtx S.Ty n} {C : S.Ty}
    (a : X.El β LambdaIter.empty), map (X.abort (C := C) a) = Y.abort (C := C) (map a)
  /-- Iteration is preserved. -/
  map_iter : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    (a : X.El β A) (b : X.El (β.snoc A) (LambdaIter.coprod B A)),
    map (X.iter a b) = Y.iter (map a) (map b)

namespace Hom

variable {X Y Z W : Alg.{u, w} S}

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
  map_iter _ _ := rfl

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
  map_iter a b := by rw [F.map_iter, G.map_iter]

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
morphism out of the syntactic model is determined by nothing at all, since
`map` of a denotation is again a denotation. -/
theorem Hom.map_denote {X Y : Alg.{u, w} S} (F : Hom X Y) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
      (h : HasType S.Instr Ctx.nil β t A),
      F.map (X.toOps.denote h) = Y.toOps.denote h
  | _, _, _, _, .fv h => absurd h (by simp [Ctx.lookup])
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
  | _, _, _, _, .iter ha hb => by
      rw [Ops.denote_iter, Ops.denote_iter, F.map_iter, F.map_denote ha,
        F.map_denote hb]

/-- A model morphism commutes with the interpretation of typing derivations. -/
@[simp] theorem Hom.map_denote' {X Y : Alg.{u, w} S} (F : Hom X Y)
    {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) :
    F.map (X.denote h) = Y.denote h := F.map_denote h

end Alg

end Isotope.LambdaIter
