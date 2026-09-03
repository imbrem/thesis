import Isotope.LambdaIter.Signature.Category
import Isotope.LambdaIter.Metatheory
import Isotope.Elgot.Basic

/-!
# Monadic models of a signature

This file supplies the *semantic* input to the algebras of the three
equational presentations (`LambdaSeq.Alg`, `LambdaCase.Alg`,
`LambdaIter.Alg`): a set-valued interpretation of a signature's type universe,
a Kleisli interpretation of its instructions in a monad, and the environments
its bound contexts denote.

## Design

* Nothing here mentions `Isotope.LambdaIter.Subtyping`.  A `Sig` deliberately
  carries no subtyping structure (see `Signature/Category.lean`), and the
  exact typing judgment has no coercion constructor, so a model of a signature
  needs none either.  This is the point of departure from
  `Isotope/LambdaIter/Subtyping/Semantics/Model.lean`, whose `TypeModel` bakes
  a proof-relevant `coe` into the interpretation.
* The two model structures are *stacked* so that the hypotheses of the three
  bridge theorems can be stated as tightly as possible.  A `SeqModel` — a bare
  interpretation of types plus Kleisli denotations of instructions — is all
  that lambda-seq consumes: it never mentions a type former.  A `Model` adds
  the four type-former equivalences, which lambda-case and lambda-iter need.
  Neither structure mentions `Iterate`: iteration enters only as a typeclass
  hypothesis on `m`, and only for lambda-iter.
* `InjectiveFormers` is the price of *coherence*.  A type universe may in
  principle identify `tensor A B` with `tensor A' B'` for `A ≠ A'`, and then
  two derivations of one term at one type can split a pair along two different
  equivalences and genuinely disagree.  Injectivity of the two binary formers
  rules this out; it holds for the freely generated `Ty α`.
-/

namespace Isotope.LambdaIter

open Isotope.Elgot

universe u v

/-- A type universe whose two binary type formers are injective.

This is exactly what makes the interpretation of a term independent of its
typing derivation: the intermediate types of a derivation are then determined
by the term and its result type, up to the slack that `abort` introduces, and
that slack is harmless because an `abort` denotation is empty. -/
class InjectiveFormers (τ : Type u) [TypeFormers τ] : Prop where
  /-- The tensor former is injective in both arguments. -/
  tensor_inj {A B A' B' : τ} : tensor A B = tensor A' B' → A = A' ∧ B = B'
  /-- The coproduct former is injective in both arguments. -/
  coprod_inj {A B A' B' : τ} : coprod A B = coprod A' B' → A = A' ∧ B = B'
  /-- A tensor is never a coproduct. -/
  tensor_ne_coprod {A B A' B' : τ} : tensor A B ≠ coprod A' B'

instance : InjectiveFormers (Ty α) where
  tensor_inj h := by
    cases h with | _ => exact ⟨rfl, rfl⟩
  coprod_inj h := by
    cases h with | _ => exact ⟨rfl, rfl⟩
  tensor_ne_coprod h := by cases h

namespace Monadic

/-- The semantic data lambda-seq consumes: an interpretation of the signature's
types and a Kleisli interpretation of its instructions, together with a
genuinely pure interpretation of the pure ones.

No type former is mentioned, and `m` is required only to be a monad. -/
structure SeqModel (S : Sig.{u}) (m : Type v → Type v) [Monad m] :
    Type (max u (v + 1)) where
  /-- The interpretation of object-language types. -/
  interp : S.Ty → Type v
  /-- The Kleisli denotation of an instruction. -/
  denoteInstr (f : S.Instr) : interp (instrSrc f) → m (interp (instrTrg f))
  /-- A pure instruction additionally has an ordinary function denotation. -/
  denotePureInstr (f : S.Instr) (hf : IsPure S.pureEff f) :
    interp (instrSrc f) → interp (instrTrg f)
  /-- The two interpretations of a pure instruction agree. -/
  denoteInstr_pure (f : S.Instr) (hf : IsPure S.pureEff f)
      (a : interp (instrSrc f)) :
    denoteInstr f a = pure (denotePureInstr f hf a)

/-- The semantic data lambda-case and lambda-iter consume: a `SeqModel`
together with an interpretation of the four type formers. -/
structure Model (S : Sig.{u}) (m : Type v → Type v) [Monad m]
    extends SeqModel.{u, v} S m where
  /-- Tensor types denote products. -/
  tensorEquiv (A B : S.Ty) : interp (tensor A B) ≃ interp A × interp B
  /-- The unit type denotes a singleton. -/
  unitEquiv : interp (unit : S.Ty) ≃ Unit
  /-- Coproduct types denote sums. -/
  coprodEquiv (A B : S.Ty) : interp (coprod A B) ≃ interp A ⊕ interp B
  /-- The empty type denotes the empty type. -/
  emptyEquiv : interp (empty : S.Ty) ≃ Empty

namespace SeqModel

variable {S : Sig.{u}} {m : Type v → Type v} [Monad m]

open LocallyNameless

/-- Environments for a length-indexed bound context.  The newest slot is the
right component. -/
def Env (M : SeqModel.{u, v} S m) : {n : Nat} → BoundCtx S.Ty n → Type v
  | _, .nil => PUnit.{v + 1}
  | _, .snoc β A => M.Env β × M.interp A

/-- Evaluate a newest-first de Bruijn index in a snoc environment. -/
def Env.get {M : SeqModel.{u, v} S m} : {n : Nat} → {β : BoundCtx S.Ty n} →
    M.Env β → (i : Fin n) → M.interp (β.get i)
  | _ + 1, .snoc _ _, ρ, i => Fin.cases ρ.2 (fun j => Env.get ρ.1 j) i

@[simp] theorem Env.get_zero {M : SeqModel.{u, v} S m} {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} (ρ : M.Env (.snoc β A)) :
    Env.get ρ (0 : Fin (n + 1)) = ρ.2 := rfl

@[simp] theorem Env.get_succ {M : SeqModel.{u, v} S m} {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} (ρ : M.Env (.snoc β A)) (i : Fin n) :
    Env.get ρ i.succ = Env.get ρ.1 i := rfl

/-- Reconstruct an environment from its newest-first dependent `Fin` view. -/
def Env.ofFun (M : SeqModel.{u, v} S m) : {n : Nat} → (β : BoundCtx S.Ty n) →
    ((i : Fin n) → M.interp (β.get i)) → M.Env β
  | 0, .nil, _ => PUnit.unit
  | _ + 1, .snoc β _, f => (Env.ofFun M β (fun i => f i.succ), f 0)

@[simp] theorem Env.get_ofFun {M : SeqModel.{u, v} S m} {n : Nat}
    (β : BoundCtx S.Ty n) (f : (i : Fin n) → M.interp (β.get i)) (i : Fin n) :
    Env.get (Env.ofFun M β f) i = f i := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih (fun k => f k.succ) j

/-- Pull an environment back along a type-preserving index renaming. -/
def Env.pull {M : SeqModel.{u, v} S m} {n k : Nat} {β : BoundCtx S.Ty n}
    {β' : BoundCtx S.Ty k} (r : TypedRenaming β β') (ρ : M.Env β') : M.Env β :=
  Env.ofFun M β fun i => r.typed i ▸ Env.get ρ (r.toFun i)

@[simp] theorem Env.get_pull {M : SeqModel.{u, v} S m} {n k : Nat}
    {β : BoundCtx S.Ty n} {β' : BoundCtx S.Ty k} (r : TypedRenaming β β')
    (ρ : M.Env β') (i : Fin n) :
    Env.get (Env.pull r ρ) i = r.typed i ▸ Env.get ρ (r.toFun i) :=
  Env.get_ofFun β _ i

@[simp] theorem Env.pull_up {M : SeqModel.{u, v} S m} {n k : Nat}
    {β : BoundCtx S.Ty n} {β' : BoundCtx S.Ty k} (r : TypedRenaming β β')
    (ρ : M.Env β') (A : S.Ty) (a : M.interp A) :
    Env.pull (r.up A) (ρ, a) = (Env.pull r ρ, a) := by
  apply Prod.ext
  · exact congrArg (Env.ofFun M β) (funext fun _ => rfl)
  · rfl

@[simp] theorem Env.pull_succ {M : SeqModel.{u, v} S m} {n : Nat}
    (β : BoundCtx S.Ty n) (A : S.Ty) (ρ : M.Env β) (a : M.interp A) :
    Env.pull (TypedRenaming.succ β A) (ρ, a) = ρ := by
  induction β with
  | nil => rfl
  | snoc β B ih =>
      apply Prod.ext
      · exact ih ρ.1
      · rfl

@[simp] theorem Env.pull_underBinder {M : SeqModel.{u, v} S m} {n : Nat}
    (β : BoundCtx S.Ty n) (X Y : S.Ty) (ρ : M.Env β) (x : M.interp X)
    (y : M.interp Y) :
    Env.pull (TypedRenaming.underBinder β X Y) ((ρ, x), y) = (ρ, y) := by
  apply Prod.ext
  · exact Env.pull_succ β X ρ x
  · rfl

@[simp] theorem Env.pull_underTwoBinders {M : SeqModel.{u, v} S m} {n : Nat}
    (β : BoundCtx S.Ty n) (X Y Z : S.Ty) (ρ : M.Env β) (x : M.interp X)
    (y : M.interp Y) (z : M.interp Z) :
    Env.pull (TypedRenaming.underTwoBinders β X Y Z) (((ρ, x), y), z) =
      ((ρ, y), z) := by
  apply Prod.ext
  · apply Prod.ext
    · exact Env.pull_succ β X ρ x
    · rfl
  · rfl

end SeqModel

end Monadic

end Isotope.LambdaIter
