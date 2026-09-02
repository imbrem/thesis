import Isotope.LambdaIter.Models.Alg
import Isotope.LambdaIter.LocallyNameless.BoundCtxMap
import Isotope.LambdaIter.Signature.Initial

/-!
# Maps of models over a signature morphism

A morphism of `Alg S` sends a carrier element at `(β, A)` to one at `(β, A)`.
Once the signature is allowed to move, a map of models over `g : S ⟶ T` must
send an element at `(β, A)` to one at `(β.map g.ty, g.ty A)`.  This file
defines that notion once and proves that such maps compose strictly, over
`𝟙` and over `≫` respectively.

Everything downstream — the total category of pairs and the fibre inclusion —
is stated in terms of `HomOver`, so the index bookkeeping is done exactly once.

## Why the laws are stated with `HEq`

A signature morphism preserves the type formers only up to a propositional
equation (`ty_tensor`, `instr_trg`, …), so `map (X.pair a b)` and
`Y.pair (map a) (map b)` live in *equal but not definitionally equal* carriers.
Writing the laws with an explicit transport makes them unusable in practice:
the composition proofs then have to shuffle transports past each other, and
`rw` cannot match under a `cast`.  Stating them as heterogeneous equalities
puts every transport where it can be eliminated by `cases`, and each law of
`HomOver.id` and `HomOver.comp` becomes a short chain of `HEq.trans`.

Transports survive in exactly five laws — `map_op`, `map_let₂`, `map_case`,
`map_abort`, `map_iter` — where an *argument* of an operation is at a
type-former type, so the term would not typecheck at all without one.

`BoundCtx.map` preserves `snoc` definitionally, so no binder clause needs a
context transport.
-/

namespace Isotope.LambdaIter

open LocallyNameless CategoryTheory

universe u w

namespace Alg

namespace Ops

variable {S T U : Sig.{u}}

/-- Transport a carrier element along equalities of its bound context and its
type.  Since `Eq` is proof irrelevant, this depends only on the endpoints. -/
def tr (X : Ops.{u, w} S) {n : Nat} {β β' : BoundCtx S.Ty n} {A A' : S.Ty}
    (hβ : β = β') (hA : A = A') (x : X.El β A) : X.El β' A' :=
  cast (by subst hβ; subst hA; rfl) x

section Tr

variable {X : Ops.{u, w} S} {n : Nat} {β β' β'' : BoundCtx S.Ty n}
  {A A' A'' : S.Ty}

/-- A transport between definitionally equal indices is the identity. -/
@[simp] theorem tr_self (h : β = β) (k : A = A) (x : X.El β A) :
    X.tr h k x = x := rfl

/-- Transports compose. -/
theorem tr_tr (h : β = β') (k : A = A') (h' : β' = β'') (k' : A' = A'')
    (x : X.El β A) :
    X.tr h' k' (X.tr h k x) = X.tr (h.trans h') (k.trans k') x := by
  cases h; cases k; rfl

/-- A transport is heterogeneously equal to what it transports. -/
theorem tr_heq (X : Ops.{u, w} S) (h : β = β') (k : A = A') (x : X.El β A) :
    HEq (X.tr h k x) x := by cases h; cases k; rfl

/-- Transport is injective. -/
theorem tr_injective (h : β = β') (k : A = A') {x y : X.El β A}
    (e : X.tr h k x = X.tr h k y) : x = y := by
  cases h; cases k; exact e

@[simp] theorem tr_eq_tr_iff (h : β = β') (k : A = A') {x y : X.El β A} :
    X.tr h k x = X.tr h k y ↔ x = y :=
  ⟨tr_injective h k, fun e => e ▸ rfl⟩

/-- An element equals a transport of itself exactly when they are
heterogeneously equal; the bridge between the two presentations. -/
theorem eq_tr_of_heq (h : β = β') (k : A = A') {x : X.El β A} {y : X.El β' A'}
    (e : HEq x y) : X.tr h k x = y := by cases h; cases k; cases e; rfl

end Tr

/-! ### Heterogeneous congruence for the twelve operations

Each of these is proved by substituting the index equations and then `rfl`.
They are what turn the identity and composition laws below into short chains.
-/

section Congr

variable (X : Ops.{u, w} S) {n : Nat} {β β' : BoundCtx S.Ty n}

theorem heq_var (hβ : β = β') (i : Fin n) :
    HEq (X.var (β := β) i) (X.var (β := β') i) := by cases hβ; rfl

theorem heq_op (hβ : β = β') (f : S.Instr)
    {a : X.El β (instrSrc f)} {a' : X.El β' (instrSrc f)} (ha : HEq a a') :
    HEq (X.op f a) (X.op f a') := by cases hβ; cases ha; rfl

theorem heq_let₁ (hβ : β = β') {A A' B B' : S.Ty} (hA : A = A') (hB : B = B')
    {a : X.El β A} {a' : X.El β' A'} (ha : HEq a a')
    {b : X.El (β.snoc A) B} {b' : X.El (β'.snoc A') B'} (hb : HEq b b') :
    HEq (X.let₁ a b) (X.let₁ a' b') := by
  cases hβ; cases hA; cases hB; cases ha; cases hb; rfl

theorem heq_unit (hβ : β = β') :
    HEq (X.unit (β := β)) (X.unit (β := β')) := by cases hβ; rfl

theorem heq_pair (hβ : β = β') {A A' B B' : S.Ty} (hA : A = A') (hB : B = B')
    {a : X.El β A} {a' : X.El β' A'} (ha : HEq a a')
    {b : X.El β B} {b' : X.El β' B'} (hb : HEq b b') :
    HEq (X.pair a b) (X.pair a' b') := by
  cases hβ; cases hA; cases hB; cases ha; cases hb; rfl

theorem heq_let₂ (hβ : β = β') {A A' B B' C C' : S.Ty} (hA : A = A')
    (hB : B = B') (hC : C = C')
    {a : X.El β (tensor A B)} {a' : X.El β' (tensor A' B')} (ha : HEq a a')
    {c : X.El ((β.snoc A).snoc B) C} {c' : X.El ((β'.snoc A').snoc B') C'}
    (hc : HEq c c') : HEq (X.let₂ a c) (X.let₂ a' c') := by
  cases hβ; cases hA; cases hB; cases hC; cases ha; cases hc; rfl

theorem heq_inl (hβ : β = β') {A A' B B' : S.Ty} (hA : A = A') (hB : B = B')
    {a : X.El β A} {a' : X.El β' A'} (ha : HEq a a') :
    HEq (X.inl (B := B) a) (X.inl (B := B') a') := by
  cases hβ; cases hA; cases hB; cases ha; rfl

theorem heq_inr (hβ : β = β') {A A' B B' : S.Ty} (hA : A = A') (hB : B = B')
    {b : X.El β B} {b' : X.El β' B'} (hb : HEq b b') :
    HEq (X.inr (A := A) b) (X.inr (A := A') b') := by
  cases hβ; cases hA; cases hB; cases hb; rfl

theorem heq_case (hβ : β = β') {A A' B B' C C' : S.Ty} (hA : A = A')
    (hB : B = B') (hC : C = C')
    {e : X.El β (coprod A B)} {e' : X.El β' (coprod A' B')} (he : HEq e e')
    {l : X.El (β.snoc A) C} {l' : X.El (β'.snoc A') C'} (hl : HEq l l')
    {r : X.El (β.snoc B) C} {r' : X.El (β'.snoc B') C'} (hr : HEq r r') :
    HEq (X.case e l r) (X.case e' l' r') := by
  cases hβ; cases hA; cases hB; cases hC; cases he; cases hl; cases hr; rfl

theorem heq_abort (hβ : β = β') {C C' : S.Ty} (hC : C = C')
    {a : X.El β empty} {a' : X.El β' empty} (ha : HEq a a') :
    HEq (X.abort (C := C) a) (X.abort (C := C') a') := by
  cases hβ; cases hC; cases ha; rfl

theorem heq_iter (hβ : β = β') {A A' B B' : S.Ty} (hA : A = A') (hB : B = B')
    {a : X.El β A} {a' : X.El β' A'} (ha : HEq a a')
    {b : X.El (β.snoc A) (coprod B A)} {b' : X.El (β'.snoc A') (coprod B' A')}
    (hb : HEq b b') : HEq (X.iter a b) (X.iter a' b') := by
  cases hβ; cases hA; cases hB; cases ha; cases hb; rfl

end Congr

end Ops

/-- A map of models **over** a signature morphism `g : S ⟶ T`: a family of maps
of carriers commuting with all twelve term formers.

Because a signature morphism preserves the type formers only propositionally,
the two sides of each law live in equal but not definitionally equal carriers;
the laws are therefore heterogeneous equalities.  See the module docstring.

This subsumes both notions of morphism in this development: a morphism of
`Alg S` is equivalent to a map over `𝟙 S` (`Alg.homOverIdEquiv`), and a
morphism of the total category is a signature morphism together with a map
over it. -/
structure HomOver {S T : Sig.{u}} (g : S ⟶ T) (X : Ops.{u, w} S)
    (Y : Ops.{u, w} T) : Type (max u w) where
  /-- The underlying family of maps of carriers. -/
  map : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty},
    X.El β A → Y.El (β.map g.ty) (g.ty A)
  /-- Variables are preserved. -/
  map_var : ∀ {n : Nat} {β : BoundCtx S.Ty n} (i : Fin n),
    HEq (map (X.var (β := β) i)) (Y.var (β := β.map g.ty) i)
  /-- Instruction application is preserved. -/
  map_op : ∀ {n : Nat} {β : BoundCtx S.Ty n} (f : S.Instr)
    (a : X.El β (instrSrc f)),
    HEq (map (X.op f a))
      (Y.op (g.instr f) (Y.tr rfl (g.instr_src f).symm (map a)))
  /-- Sequencing is preserved. -/
  map_let₁ : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    (a : X.El β A) (b : X.El (β.snoc A) B),
    HEq (map (X.let₁ a b)) (Y.let₁ (map a) (map b))
  /-- The unit value is preserved. -/
  map_unit : ∀ {n : Nat} {β : BoundCtx S.Ty n},
    HEq (map (X.unit (β := β))) (Y.unit (β := β.map g.ty))
  /-- Pairing is preserved. -/
  map_pair : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    (a : X.El β A) (b : X.El β B),
    HEq (map (X.pair a b)) (Y.pair (map a) (map b))
  /-- Pair elimination is preserved. -/
  map_let₂ : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty}
    (a : X.El β (tensor A B)) (c : X.El ((β.snoc A).snoc B) C),
    HEq (map (X.let₂ a c))
      (Y.let₂ (Y.tr rfl (g.ty_tensor A B) (map a)) (map c))
  /-- Left injection is preserved. -/
  map_inl : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} (a : X.El β A),
    HEq (map (X.inl (B := B) a)) (Y.inl (B := g.ty B) (map a))
  /-- Right injection is preserved. -/
  map_inr : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} (b : X.El β B),
    HEq (map (X.inr (A := A) b)) (Y.inr (A := g.ty A) (map b))
  /-- Case analysis is preserved. -/
  map_case : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B C : S.Ty}
    (e : X.El β (coprod A B)) (l : X.El (β.snoc A) C) (r : X.El (β.snoc B) C),
    HEq (map (X.case e l r))
      (Y.case (Y.tr rfl (g.ty_coprod A B) (map e)) (map l) (map r))
  /-- Empty elimination is preserved. -/
  map_abort : ∀ {n : Nat} {β : BoundCtx S.Ty n} {C : S.Ty} (a : X.El β empty),
    HEq (map (X.abort (C := C) a))
      (Y.abort (C := g.ty C) (Y.tr rfl g.ty_empty (map a)))
  /-- Iteration is preserved. -/
  map_iter : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    (a : X.El β A) (b : X.El (β.snoc A) (coprod B A)),
    HEq (map (X.iter a b)) (Y.iter (map a) (Y.tr rfl (g.ty_coprod B A) (map b)))

namespace HomOver

variable {S T U : Sig.{u}} {X : Ops.{u, w} S} {Y : Ops.{u, w} T}
  {Z : Ops.{u, w} U} {g : S ⟶ T} {h : T ⟶ U}

/-- Two maps over the same signature morphism agree as soon as their carrier
maps do. -/
@[ext] theorem ext {F G : HomOver g X Y}
    (e : ∀ {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty} (x : X.El β A),
      F.map x = G.map x) : F = G := by
  cases F; cases G
  congr 1
  funext n β A x
  exact e x

/-- The carrier map respects heterogeneous equality of its arguments. -/
theorem mapHeq (F : HomOver g X Y) {n : Nat} {β β' : BoundCtx S.Ty n}
    (hβ : β = β') {A A' : S.Ty} (hA : A = A') {x : X.El β A} {x' : X.El β' A'}
    (hx : HEq x x') : HEq (F.map x) (F.map x') := by
  cases hβ; cases hA; cases hx; rfl

/-- The carrier map commutes with transport. -/
theorem map_tr (F : HomOver g X Y) {n : Nat} {β β' : BoundCtx S.Ty n}
    {A A' : S.Ty} (hβ : β = β') (hA : A = A') (x : X.El β A) :
    F.map (X.tr hβ hA x) =
      Y.tr (congrArg (BoundCtx.map g.ty) hβ) (congrArg g.ty hA) (F.map x) := by
  cases hβ; cases hA; rfl

/-! ### The identity -/

/-- The identity map of models, over the identity signature morphism.  Its only
content is the transport along `BoundCtx.map_id`. -/
def id (X : Ops.{u, w} S) : HomOver (𝟙 S) X X where
  map {_n β _A} x := X.tr (BoundCtx.map_id β).symm rfl x
  map_var i :=
    (Ops.tr_heq _ _ _ _).trans (Ops.heq_var X (BoundCtx.map_id _).symm i)
  map_op f _a :=
    (Ops.tr_heq _ _ _ _).trans
      (Ops.heq_op X (BoundCtx.map_id _).symm f
        ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm)
  map_let₁ _a _b :=
    (Ops.tr_heq _ _ _ _).trans
      (Ops.heq_let₁ X (BoundCtx.map_id _).symm rfl rfl
        (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm)
  map_unit :=
    (Ops.tr_heq _ _ _ _).trans (Ops.heq_unit X (BoundCtx.map_id _).symm)
  map_pair _a _b :=
    (Ops.tr_heq _ _ _ _).trans
      (Ops.heq_pair X (BoundCtx.map_id _).symm rfl rfl
        (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm)
  map_let₂ _a _c :=
    (Ops.tr_heq _ _ _ _).trans
      (Ops.heq_let₂ X (BoundCtx.map_id _).symm rfl rfl rfl
        ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm
        (Ops.tr_heq _ _ _ _).symm)
  map_inl _a :=
    (Ops.tr_heq _ _ _ _).trans
      (Ops.heq_inl X (BoundCtx.map_id _).symm rfl rfl
        (Ops.tr_heq _ _ _ _).symm)
  map_inr _b :=
    (Ops.tr_heq _ _ _ _).trans
      (Ops.heq_inr X (BoundCtx.map_id _).symm rfl rfl
        (Ops.tr_heq _ _ _ _).symm)
  map_case _e _l _r :=
    (Ops.tr_heq _ _ _ _).trans
      (Ops.heq_case X (BoundCtx.map_id _).symm rfl rfl rfl
        ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm
        (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm)
  map_abort _a :=
    (Ops.tr_heq _ _ _ _).trans
      (Ops.heq_abort X (BoundCtx.map_id _).symm rfl
        ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm)
  map_iter _a _b :=
    (Ops.tr_heq _ _ _ _).trans
      (Ops.heq_iter X (BoundCtx.map_id _).symm rfl rfl
        (Ops.tr_heq _ _ _ _).symm
        ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm)

@[simp] theorem id_map (X : Ops.{u, w} S) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} (x : X.El β A) :
    (HomOver.id X).map x = X.tr (BoundCtx.map_id β).symm rfl x := rfl

/-! ### Composition -/

/-- Composition of maps of models, over the composite signature morphism.  Its
only content is the transport along `BoundCtx.map_comp`. -/
def comp (F : HomOver g X Y) (G : HomOver h Y Z) : HomOver (g ≫ h) X Z where
  map {_n β _A} x :=
    Z.tr (BoundCtx.map_comp g.ty h.ty β).symm rfl (G.map (F.map x))
  map_var i :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl (BoundCtx.map_get g.ty _ i).symm (F.map_var i)).trans
        (G.map_var i)).trans
        (Ops.heq_var Z (BoundCtx.map_comp g.ty h.ty _).symm i))
  map_op f a :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl (g.instr_trg f).symm (F.map_op f a)).trans
        (G.map_op (g.instr f) _)).trans
        (Ops.heq_op Z (BoundCtx.map_comp g.ty h.ty _).symm _
          ((Ops.tr_heq _ _ _ _).trans
            ((G.mapHeq rfl (g.instr_src f) (Ops.tr_heq _ _ _ _)).trans
              ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm))))
  map_let₁ a b :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl rfl (F.map_let₁ a b)).trans (G.map_let₁ _ _)).trans
        (Ops.heq_let₁ Z (BoundCtx.map_comp g.ty h.ty _).symm rfl rfl
          (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm))
  map_unit :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl g.ty_unit F.map_unit).trans G.map_unit).trans
        (Ops.heq_unit Z (BoundCtx.map_comp g.ty h.ty _).symm))
  map_pair a b :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl (g.ty_tensor _ _) (F.map_pair a b)).trans
        (G.map_pair _ _)).trans
        (Ops.heq_pair Z (BoundCtx.map_comp g.ty h.ty _).symm rfl rfl
          (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm))
  map_let₂ a c :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl rfl (F.map_let₂ a c)).trans (G.map_let₂ _ _)).trans
        (Ops.heq_let₂ Z (BoundCtx.map_comp g.ty h.ty _).symm rfl rfl rfl
          ((Ops.tr_heq _ _ _ _).trans
            ((G.mapHeq rfl (g.ty_tensor _ _).symm (Ops.tr_heq _ _ _ _)).trans
              ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm))
          (Ops.tr_heq _ _ _ _).symm))
  map_inl a :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl (g.ty_coprod _ _) (F.map_inl a)).trans
        (G.map_inl _)).trans
        (Ops.heq_inl Z (BoundCtx.map_comp g.ty h.ty _).symm rfl rfl
          (Ops.tr_heq _ _ _ _).symm))
  map_inr b :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl (g.ty_coprod _ _) (F.map_inr b)).trans
        (G.map_inr _)).trans
        (Ops.heq_inr Z (BoundCtx.map_comp g.ty h.ty _).symm rfl rfl
          (Ops.tr_heq _ _ _ _).symm))
  map_case e l r :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl rfl (F.map_case e l r)).trans (G.map_case _ _ _)).trans
        (Ops.heq_case Z (BoundCtx.map_comp g.ty h.ty _).symm rfl rfl rfl
          ((Ops.tr_heq _ _ _ _).trans
            ((G.mapHeq rfl (g.ty_coprod _ _).symm (Ops.tr_heq _ _ _ _)).trans
              ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm))
          (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm))
  map_abort a :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl rfl (F.map_abort a)).trans (G.map_abort _)).trans
        (Ops.heq_abort Z (BoundCtx.map_comp g.ty h.ty _).symm rfl
          ((Ops.tr_heq _ _ _ _).trans
            ((G.mapHeq rfl g.ty_empty.symm (Ops.tr_heq _ _ _ _)).trans
              ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm))))
  map_iter a b :=
    (Ops.tr_heq _ _ _ _).trans
      (((G.mapHeq rfl rfl (F.map_iter a b)).trans (G.map_iter _ _)).trans
        (Ops.heq_iter Z (BoundCtx.map_comp g.ty h.ty _).symm rfl rfl
          (Ops.tr_heq _ _ _ _).symm
          ((Ops.tr_heq _ _ _ _).trans
            ((G.mapHeq rfl (g.ty_coprod _ _).symm (Ops.tr_heq _ _ _ _)).trans
              ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm))))

@[simp] theorem comp_map (F : HomOver g X Y) (G : HomOver h Y Z) {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} (x : X.El β A) :
    (F.comp G).map x =
      Z.tr (BoundCtx.map_comp g.ty h.ty β).symm rfl (G.map (F.map x)) := rfl

end HomOver

namespace Hom

/-- A morphism of models commutes with transport.

Shared-namespace note: this is a lemma about `Alg.Hom`, defined in
`Models/Alg.lean`. -/
theorem map_tr {S : Sig.{u}} {X Y : Alg.{u, w} S} (F : X ⟶ Y) {n : Nat}
    {β β' : BoundCtx S.Ty n} {A A' : S.Ty} (hβ : β = β') (hA : A = A')
    (x : X.El β A) :
    F.map (X.toOps.tr hβ hA x) = Y.toOps.tr hβ hA (F.map x) := by
  cases hβ; cases hA; rfl

end Hom

end Alg

end Isotope.LambdaIter
