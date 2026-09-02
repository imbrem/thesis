import Isotope.LambdaIter.Models.Alg
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

The last two give worked morphisms that are visibly *not* identities: the two
projections out of `X ⨯ Y`, and the endomorphism of `X ^ Bool` induced by
`not`.

## Honest boundary

Every algebra constructed here is built from an algebra already given, or is
the terminal one.  Nothing in this file constructs an algebra with semantic
content — for instance one arising from a monad or a Freyd category — and
nothing here should be read as evidence that such an algebra exists.  See the
module docstring of `Isotope/LambdaIter/Models/Alg.lean`.
-/

namespace Isotope.LambdaIter

open LocallyNameless CategoryTheory

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
  unit := PUnit.unit
  pair _ _ := PUnit.unit
  let₂ _ _ := PUnit.unit
  inl _ := PUnit.unit
  inr _ := PUnit.unit
  case _ _ _ := PUnit.unit
  abort _ := PUnit.unit
  iter _ _ := PUnit.unit
  coh _ _ := Subsingleton.elim _ _
  sound _ _ _ := Subsingleton.elim _ _

@[simp] theorem terminal_El {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty} :
    (terminal.{u, w} S).El β A = PUnit := rfl

/-- There is exactly one morphism into the terminal model. -/
instance uniqueToTerminal (X : Alg.{u, w} S) : Unique (X ⟶ terminal.{u, w} S) where
  default :=
    { map := fun _ => PUnit.unit
      map_var := fun _ => rfl
      map_op := fun _ _ => rfl
      map_let₁ := fun _ _ => rfl
      map_unit := rfl
      map_pair := fun _ _ => rfl
      map_let₂ := fun _ _ => rfl
      map_inl := fun _ => rfl
      map_inr := fun _ => rfl
      map_case := fun _ _ _ => rfl
      map_abort := fun _ => rfl
      map_iter := fun _ _ => rfl }
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
  unit := (X.unit, Y.unit)
  pair a b := (X.pair a.1 b.1, Y.pair a.2 b.2)
  let₂ a c := (X.let₂ a.1 c.1, Y.let₂ a.2 c.2)
  inl a := (X.inl a.1, Y.inl a.2)
  inr b := (X.inr b.1, Y.inr b.2)
  case e l r := (X.case e.1 l.1 r.1, Y.case e.2 l.2 r.2)
  abort a := (X.abort a.1, Y.abort a.2)
  iter a b := (X.iter a.1 b.1, Y.iter a.2 b.2)

/-- Denotation in the product model is the pair of denotations. -/
theorem denote_prodOps (X Y : Alg.{u, w} S) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
      (h : HasType S.Instr Ctx.nil β t A),
      (prodOps X Y).denote h = (X.toOps.denote h, Y.toOps.denote h)
  | _, _, _, _, .fv h => absurd h (by simp [Ctx.lookup])
  | _, _, _, _, .bv => rfl
  | _, _, _, _, .op ha => by
      simp only [Ops.denote_op, denote_prodOps X Y ha]; rfl
  | _, _, _, _, .let₁ ha hb => by
      simp only [Ops.denote_let₁, denote_prodOps X Y ha, denote_prodOps X Y hb]; rfl
  | _, _, _, _, .unit => rfl
  | _, _, _, _, .pair ha hb => by
      simp only [Ops.denote_pair, denote_prodOps X Y ha, denote_prodOps X Y hb]; rfl
  | _, _, _, _, .let₂ ha hc => by
      simp only [Ops.denote_let₂, denote_prodOps X Y ha, denote_prodOps X Y hc]; rfl
  | _, _, _, _, .inl ha => by
      simp only [Ops.denote_inl, denote_prodOps X Y ha]; rfl
  | _, _, _, _, .inr hb => by
      simp only [Ops.denote_inr, denote_prodOps X Y hb]; rfl
  | _, _, _, _, .case he hl hr => by
      simp only [Ops.denote_case, denote_prodOps X Y he, denote_prodOps X Y hl,
        denote_prodOps X Y hr]; rfl
  | _, _, _, _, .abort ha => by
      simp only [Ops.denote_abort, denote_prodOps X Y ha]; rfl
  | _, _, _, _, .iter ha hb => by
      simp only [Ops.denote_iter, denote_prodOps X Y ha, denote_prodOps X Y hb]; rfl

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
  map_unit := rfl
  map_pair _ _ := rfl
  map_let₂ _ _ := rfl
  map_inl _ := rfl
  map_inr _ := rfl
  map_case _ _ _ := rfl
  map_abort _ := rfl
  map_iter _ _ := rfl

/-- Second projection out of a product of models. -/
def snd (X Y : Alg.{u, w} S) : prod X Y ⟶ Y where
  map p := p.2
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

/-- Pairing of two morphisms into a product of models. -/
def lift {Z X Y : Alg.{u, w} S} (F : Z ⟶ X) (G : Z ⟶ Y) : Z ⟶ prod X Y where
  map z := (F.map z, G.map z)
  map_var i := by rw [F.map_var, G.map_var]; rfl
  map_op f a := by rw [F.map_op, G.map_op]; rfl
  map_let₁ a b := by rw [F.map_let₁, G.map_let₁]; rfl
  map_unit := by intro n β; rw [F.map_unit, G.map_unit]; rfl
  map_pair a b := by rw [F.map_pair, G.map_pair]; rfl
  map_let₂ a c := by rw [F.map_let₂, G.map_let₂]; rfl
  map_inl a := by rw [F.map_inl, G.map_inl]; rfl
  map_inr b := by rw [F.map_inr, G.map_inr]; rfl
  map_case e l r := by rw [F.map_case, G.map_case]; rfl
  map_abort a := by rw [F.map_abort, G.map_abort]; rfl
  map_iter a b := by rw [F.map_iter, G.map_iter]; rfl

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
  unit _ := X.unit
  pair a b x := X.pair (a x) (b x)
  let₂ a c x := X.let₂ (a x) (c x)
  inl a x := X.inl (a x)
  inr b x := X.inr (b x)
  case e l r x := X.case (e x) (l x) (r x)
  abort a x := X.abort (a x)
  iter a b x := X.iter (a x) (b x)

/-- Denotation in a power model is the constant family of denotations. -/
theorem denote_powOps (W : Type w) (X : Alg.{u, w} S) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
      (h : HasType S.Instr Ctx.nil β t A),
      (powOps W X).denote h = fun _ => X.toOps.denote h
  | _, _, _, _, .fv h => absurd h (by simp [Ctx.lookup])
  | _, _, _, _, .bv => rfl
  | _, _, _, _, .op ha => by
      simp only [Ops.denote_op, denote_powOps W X ha]; rfl
  | _, _, _, _, .let₁ ha hb => by
      simp only [Ops.denote_let₁, denote_powOps W X ha, denote_powOps W X hb]; rfl
  | _, _, _, _, .unit => rfl
  | _, _, _, _, .pair ha hb => by
      simp only [Ops.denote_pair, denote_powOps W X ha, denote_powOps W X hb]; rfl
  | _, _, _, _, .let₂ ha hc => by
      simp only [Ops.denote_let₂, denote_powOps W X ha, denote_powOps W X hc]; rfl
  | _, _, _, _, .inl ha => by
      simp only [Ops.denote_inl, denote_powOps W X ha]; rfl
  | _, _, _, _, .inr hb => by
      simp only [Ops.denote_inr, denote_powOps W X hb]; rfl
  | _, _, _, _, .case he hl hr => by
      simp only [Ops.denote_case, denote_powOps W X he, denote_powOps W X hl,
        denote_powOps W X hr]; rfl
  | _, _, _, _, .abort ha => by
      simp only [Ops.denote_abort, denote_powOps W X ha]; rfl
  | _, _, _, _, .iter ha hb => by
      simp only [Ops.denote_iter, denote_powOps W X ha, denote_powOps W X hb]; rfl

/-- The power of a model by a bare type. -/
def pow (W : Type w) (X : Alg.{u, w} S) : Alg.{u, w} S where
  toOps := powOps W X
  coh h k := by rw [denote_powOps, denote_powOps, X.coh h k]
  sound h k e := by rw [denote_powOps, denote_powOps, X.sound h k e]

/-- Reindexing a power along a map of index types.  Contravariant, and
manifestly not an identity in general: see `powReindex_not_id` below. -/
def powReindex {W W' : Type w} (v : W' → W) (X : Alg.{u, w} S) :
    pow W X ⟶ pow W' X where
  map a := a ∘ v
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

@[simp] theorem powReindex_id (W : Type w) (X : Alg.{u, w} S) :
    powReindex (id : W → W) X = 𝟙 (pow W X) := rfl

@[simp] theorem powReindex_comp {W W' W'' : Type w} (v : W' → W) (v' : W'' → W')
    (X : Alg.{u, w} S) :
    powReindex v X ≫ powReindex v' X = powReindex (v ∘ v') X := rfl

end Alg

end Isotope.LambdaIter
