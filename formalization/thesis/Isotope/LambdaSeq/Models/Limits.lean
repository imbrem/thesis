import Isotope.LambdaSeq.Models.Alg
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Terminal object, binary products, and powers in the category of models

`Alg S` is not an empty category, and its morphisms are not all identities.
This file proves both, by constructing:

* the **terminal model** (every carrier a singleton), which is the honest
  non-vacuity witness for statements of the form `Unique (Syn ⟶ X)`: without
  it such a statement could be about a class nothing inhabits;
* **binary products** of models, with the full universal property as a
  `CategoryTheory.Limits.IsLimit`, hence `HasBinaryProducts (Alg S)`;
* **powers** `X ^ W` by a bare type `W`, functorially contravariant in `W`.

## Honest boundary

Every algebra constructed here is built from an algebra already given, or is
the terminal one.  Nothing in this file constructs an algebra with semantic
content — for instance one arising from a monad or a Freyd category — and
nothing here should be read as evidence that such an algebra exists.  See the
module docstring of `Isotope/LambdaSeq/Models/Alg.lean`.
-/

namespace Isotope.LambdaSeq

open LocallyNameless CategoryTheory

open Isotope.LambdaIter (Sig)

universe u w

namespace Alg

variable {S : Sig.{u}}

/-! ### The terminal model -/

/-- The terminal model: every carrier is a singleton. -/
def terminal (S : Sig.{u}) : Alg.{u, w} S where
  El _ _ := PUnit
  var _ := PUnit.unit
  op _ _ := PUnit.unit
  let₁ _ _ := PUnit.unit
  coh _ _ := Subsingleton.elim _ _
  sound _ _ _ := Subsingleton.elim _ _

@[simp] theorem terminal_El {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty} :
    (terminal.{u, w} S).El β A = PUnit := rfl

/-- There is exactly one morphism into the terminal model. -/
instance uniqueToTerminal (X : Alg.{u, w} S) :
    Unique (X ⟶ terminal.{u, w} S) where
  default :=
    { map := fun _ => PUnit.unit
      map_var := fun _ => rfl
      map_op := fun _ _ => rfl
      map_let₁ := fun _ _ => rfl }
  uniq F := by
    apply Alg.Hom.ext
    intro n β A x
    rfl

/-- `Alg.terminal` really is terminal. -/
def terminalIsTerminal (S : Sig.{u}) : Limits.IsTerminal (terminal.{u, w} S) :=
  Limits.IsTerminal.ofUnique _

instance : Limits.HasTerminal (Alg.{u, w} S) :=
  Limits.hasTerminal_of_unique (terminal.{u, w} S)

/-! ### Binary products -/

/-- The operations of the product model, componentwise. -/
def prodOps (X Y : Alg.{u, w} S) : Ops.{u, w} S where
  El β A := X.El β A × Y.El β A
  var i := (X.var i, Y.var i)
  op f a := (X.op f a.1, Y.op f a.2)
  let₁ a b := (X.let₁ a.1 b.1, Y.let₁ a.2 b.2)

/-- Denotation in the product model is the pair of denotations. -/
theorem denote_prodOps (X Y : Alg.{u, w} S) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
      (h : HasType S.Instr LambdaIter.Ctx.nil β t A),
      (prodOps X Y).denote h = (X.toOps.denote h, Y.toOps.denote h)
  | _, _, _, _, .fv h => absurd h (by simp [LambdaIter.Ctx.lookup])
  | _, _, _, _, .bv => rfl
  | _, _, _, _, .op ha => by
      simp only [Ops.denote_op, denote_prodOps X Y ha]; rfl
  | _, _, _, _, .let₁ ha hb => by
      simp only [Ops.denote_let₁, denote_prodOps X Y ha, denote_prodOps X Y hb]
      rfl

/-- The product of two models. -/
def prod (X Y : Alg.{u, w} S) : Alg.{u, w} S where
  toOps := prodOps X Y
  coh h k := by rw [denote_prodOps, denote_prodOps, X.coh h k, Y.coh h k]
  sound h k e := by
    rw [denote_prodOps, denote_prodOps, X.sound h k e, Y.sound h k e]

/-- First projection out of a product of models. -/
def fst (X Y : Alg.{u, w} S) : prod X Y ⟶ X where
  map p := p.1
  map_var _ := rfl
  map_op _ _ := rfl
  map_let₁ _ _ := rfl

/-- Second projection out of a product of models. -/
def snd (X Y : Alg.{u, w} S) : prod X Y ⟶ Y where
  map p := p.2
  map_var _ := rfl
  map_op _ _ := rfl
  map_let₁ _ _ := rfl

/-- Pairing of two morphisms into a product of models. -/
def lift {Z X Y : Alg.{u, w} S} (F : Z ⟶ X) (G : Z ⟶ Y) : Z ⟶ prod X Y where
  map z := (F.map z, G.map z)
  map_var i := by rw [F.map_var, G.map_var]; rfl
  map_op f a := by rw [F.map_op, G.map_op]; rfl
  map_let₁ a b := by rw [F.map_let₁, G.map_let₁]; rfl

@[simp] theorem lift_fst {Z X Y : Alg.{u, w} S} (F : Z ⟶ X) (G : Z ⟶ Y) :
    lift F G ≫ fst X Y = F := rfl

@[simp] theorem lift_snd {Z X Y : Alg.{u, w} S} (F : Z ⟶ X) (G : Z ⟶ Y) :
    lift F G ≫ snd X Y = G := rfl

/-- The product of models has the universal property of a binary product. -/
def prodIsLimit (X Y : Alg.{u, w} S) :
    Limits.IsLimit (Limits.BinaryFan.mk (fst X Y) (snd X Y)) :=
  Limits.BinaryFan.isLimitMk (fun s => lift s.fst s.snd) (fun _ => rfl)
    (fun _ => rfl) (fun s m h1 h2 => by
      apply Alg.Hom.ext
      intro n β A z
      have e1 := congrArg (fun F : s.pt ⟶ X => F.map z) h1
      have e2 := congrArg (fun G : s.pt ⟶ Y => G.map z) h2
      exact Prod.ext e1 e2)

instance hasBinaryProduct (X Y : Alg.{u, w} S) : Limits.HasBinaryProduct X Y :=
  ⟨⟨⟨_, prodIsLimit X Y⟩⟩⟩

instance : Limits.HasBinaryProducts (Alg.{u, w} S) :=
  Limits.hasBinaryProducts_of_hasLimit_pair _

/-- The diagonal, a worked non-identity morphism. -/
def diag (X : Alg.{u, w} S) : X ⟶ prod X X := lift (𝟙 X) (𝟙 X)

/-! ### Powers by a bare type -/

/-- The operations of the power model `X ^ W`, pointwise in `W`. -/
def powOps (W : Type w) (X : Alg.{u, w} S) : Ops.{u, w} S where
  El β A := W → X.El β A
  var i _ := X.var i
  op f a x := X.op f (a x)
  let₁ a b x := X.let₁ (a x) (b x)

/-- Denotation in a power model is the constant family of denotations. -/
theorem denote_powOps (W : Type w) (X : Alg.{u, w} S) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
      (h : HasType S.Instr LambdaIter.Ctx.nil β t A),
      (powOps W X).denote h = fun _ => X.toOps.denote h
  | _, _, _, _, .fv h => absurd h (by simp [LambdaIter.Ctx.lookup])
  | _, _, _, _, .bv => rfl
  | _, _, _, _, .op ha => by
      simp only [Ops.denote_op, denote_powOps W X ha]; rfl
  | _, _, _, _, .let₁ ha hb => by
      simp only [Ops.denote_let₁, denote_powOps W X ha, denote_powOps W X hb]
      rfl

/-- The power of a model by a bare type. -/
def pow (W : Type w) (X : Alg.{u, w} S) : Alg.{u, w} S where
  toOps := powOps W X
  coh h k := by rw [denote_powOps, denote_powOps, X.coh h k]
  sound h k e := by rw [denote_powOps, denote_powOps, X.sound h k e]

/-- Reindexing a power along a map of index types.  Contravariant, and
manifestly not an identity in general: see `powReindex_ne_id`. -/
def powReindex {W W' : Type w} (v : W' → W) (X : Alg.{u, w} S) :
    pow W X ⟶ pow W' X where
  map a := a ∘ v
  map_var _ := rfl
  map_op _ _ := rfl
  map_let₁ _ _ := rfl

@[simp] theorem powReindex_id (W : Type w) (X : Alg.{u, w} S) :
    powReindex (id : W → W) X = 𝟙 (pow W X) := rfl

@[simp] theorem powReindex_comp {W W' W'' : Type w} (v : W' → W) (v' : W'' → W')
    (X : Alg.{u, w} S) :
    powReindex v X ≫ powReindex v' X = powReindex (v ∘ v') X := rfl

end Alg

end Isotope.LambdaSeq
