import Isotope.LambdaSeq.Typing
import Isotope.LambdaIter.Semantics.Categorical

/-! # Freyd-category semantics of lambda-seq -/

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Isotope.LambdaSeq.Semantics.Categorical

open CategoryTheory CategoryTheory.Category
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory

/-- A LambdaSeq type model only interprets types and subtyping.  In particular, it does not
ask the value category for coproducts or ask that object-language type formers be preserved. -/
class TypeModel (τ : Type u₃) [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
    (V : Type u₁) [Category.{v₁} V] where
  obj : τ → V
  subty {A B : τ} : LambdaIter.Subty A B → (obj A ⟶ obj B)

class InstructionModel [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
    [Category.{v₁} V] [Category.{v₂} C] (J : Functor V C)
    (M : TypeModel τ V) (Φ : Type u₄) [LambdaIter.HasTy Φ τ] where
  denote (f : Φ) : J.obj (M.obj (LambdaIter.instrSrc f)) ⟶
    J.obj (M.obj (LambdaIter.instrTrg f))

section Contexts

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ] (M : TypeModel τ V)

def ctxObj : LambdaIter.Ctx ν τ → V
  | .nil => 𝟙_ V
  | .snoc Γ _ A => ctxObj Γ ⊗ M.obj A

def boundObj : {n : Nat} → LambdaSeq.LocallyNameless.BoundCtx τ n → V
  | 0, .nil => 𝟙_ V
  | _ + 1, .snoc β A => boundObj β ⊗ M.obj A

def envObj (Γ : LambdaIter.Ctx ν τ) {n : Nat}
    (β : LambdaSeq.LocallyNameless.BoundCtx τ n) : V := ctxObj M Γ ⊗ boundObj M β

noncomputable def ctxLookup [DecidableEq ν] : {Γ : LambdaIter.Ctx ν τ} →
    (x : ν) → {A : τ} → Γ.lookup x = some A → (ctxObj M Γ ⟶ M.obj A)
  | .nil, _, _, h => by simp [LambdaIter.Ctx.lookup] at h
  | .snoc Γ none B, x, A, h =>
      CartesianMonoidalCategory.fst _ _ ≫ ctxLookup x h
  | .snoc Γ (some y) B, x, A, h => by
      by_cases hxy : x = y
      · subst y
        simp [LambdaIter.Ctx.lookup] at h
        cases h
        exact CartesianMonoidalCategory.snd _ _
      · exact CartesianMonoidalCategory.fst _ _ ≫
          ctxLookup x (by simpa [LambdaIter.Ctx.lookup, hxy] using h)

noncomputable def freeLookup [DecidableEq ν] {Γ : LambdaIter.Ctx ν τ}
    {n : Nat} {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    (x : ν) {A : τ} (h : Γ.lookup x = some A) : envObj M Γ β ⟶ M.obj A :=
  CartesianMonoidalCategory.fst _ _ ≫ ctxLookup M x h

noncomputable def boundLookup : {n : Nat} → {β : LambdaSeq.LocallyNameless.BoundCtx τ n} →
    (i : Fin n) → (boundObj M β ⟶ M.obj (β.get i))
  | _ + 1, .snoc β A, i => Fin.cases
      (CartesianMonoidalCategory.snd _ _)
      (fun j => CartesianMonoidalCategory.fst _ _ ≫ boundLookup j) i

noncomputable def boundVar {Γ : LambdaIter.Ctx ν τ}
    {n : Nat} {β : LambdaSeq.LocallyNameless.BoundCtx τ n} (i : Fin n) :
    envObj M Γ β ⟶ M.obj (β.get i) :=
  CartesianMonoidalCategory.snd _ _ ≫ boundLookup M i

def envSnocIso (Γ : LambdaIter.Ctx ν τ) {n : Nat}
    (β : LambdaSeq.LocallyNameless.BoundCtx τ n) (A : τ) :
    envObj M Γ β ⊗ M.obj A ≅ envObj M Γ (.snoc β A) :=
  α_ (ctxObj M Γ) (boundObj M β) (M.obj A)

end Contexts

section Denotation

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : Functor V C) [FreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type*} [LambdaIter.HasTy Φ τ] [InstructionModel J M Φ]

/-- LambdaSeq denotes in any Freyd category; no distributivity, coproduct, or Elgot structure
is present in the assumptions. -/
noncomputable def denote : {Γ : LambdaIter.Ctx ν τ} → {n : Nat} →
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n} →
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} → {A : τ} →
    LambdaSeq.LocallyNameless.HasType Φ Γ β t A →
      (J.obj (envObj M Γ β) ⟶ J.obj (M.obj A))
  | _, _, _, _, _, .fv h => J.map (freeLookup M _ h)
  | _, _, _, _, _, .bv => J.map (boundVar M _)
  | _, _, _, _, _, .op ha => denote ha ≫ InstructionModel.denote _
  | Γ, _, β, _, _, .let₁ ha hb =>
      LambdaIter.Subtyping.Semantics.Categorical.bind J (denote ha) <|
        J.map (envSnocIso M Γ β _).hom ≫ denote hb

end Denotation
end Isotope.LambdaSeq.Semantics.Categorical

namespace Isotope.LambdaSeq.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category
open CategoryTheory.PremonoidalCategory

open scoped MonoidalCategory

section Denotation

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : Functor V C) [FreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : Isotope.LambdaSeq.Semantics.Categorical.TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type*} [LambdaIter.HasTy Φ τ]
  [Isotope.LambdaSeq.Semantics.Categorical.InstructionModel J M Φ]

/-- Categorical denotation of the proof-relevant coercive sequential judgment. -/
noncomputable def denote : {Γ : LambdaIter.Ctx ν τ} → {n : Nat} →
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n} →
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} → {A : τ} →
    LambdaSeq.Subtyping.LocallyNameless.HasType Φ Γ β t A →
      (J.obj (Isotope.LambdaSeq.Semantics.Categorical.envObj M Γ β) ⟶ J.obj (M.obj A))
  | _, _, _, _, _, .fv h =>
      J.map (Isotope.LambdaSeq.Semantics.Categorical.freeLookup M _ h)
  | _, _, _, _, _, .bv => J.map (Isotope.LambdaSeq.Semantics.Categorical.boundVar M _)
  | _, _, _, _, _, .op ha => denote ha ≫
      Isotope.LambdaSeq.Semantics.Categorical.InstructionModel.denote _
  | Γ, _, β, _, _, .let₁ ha hb =>
      LambdaIter.Subtyping.Semantics.Categorical.bind J (denote ha) <|
        J.map (Isotope.LambdaSeq.Semantics.Categorical.envSnocIso M Γ β _).hom ≫ denote hb
  | _, _, _, _, _, .sub ha d => denote ha ≫ J.map (M.subty d)

end Denotation
end Isotope.LambdaSeq.Subtyping.Semantics.Categorical
