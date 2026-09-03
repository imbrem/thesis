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

/-- Restrict a lambda-iter type model to the structure used by lambda-seq. -/
@[reducible] noncomputable def TypeModel.ofIter
    [Category.{v₁} V] [CartesianMonoidalCategory V]
    [CategoryTheory.Limits.HasFiniteCoproducts V]
    [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
    (M : LambdaIter.Subtyping.Semantics.Categorical.TypeModel τ V) :
    TypeModel τ V where
  obj := M.obj
  subty := M.subty

/-- Restrict a lambda-iter instruction model along `TypeModel.ofIter`. -/
@[reducible] noncomputable def InstructionModel.ofIter
    [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V]
    [CategoryTheory.Limits.HasFiniteCoproducts V]
    [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
    [LambdaIter.HasTy Φ τ]
    (J : Functor V C)
    (M : LambdaIter.Subtyping.Semantics.Categorical.TypeModel τ V)
    [LambdaIter.Subtyping.Semantics.Categorical.InstructionModel J M Φ] :
    InstructionModel J (TypeModel.ofIter M) Φ where
  denote := LambdaIter.Subtyping.Semantics.Categorical.InstructionModel.denote

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

section IterRestriction

open CategoryTheory.Limits

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : LambdaIter.Subtyping.Semantics.Categorical.TypeModel τ V)

/-- Change only the source object of a morphism along an object equality. -/
def transportSrc {X X' Y : V} (e : X = X') (f : X ⟶ Y) : X' ⟶ Y :=
  eqToHom e.symm ≫ f

@[simp] theorem transportSrc_rfl {X Y : V} (f : X ⟶ Y) :
    transportSrc rfl f = f := by simp [transportSrc]

theorem transportSrc_tensor_fst {X X' Z Y : V} (e : X = X') (f : X ⟶ Y) :
    transportSrc (congrArg (fun W => W ⊗ Z) e)
        (CartesianMonoidalCategory.fst X Z ≫ f) =
      CartesianMonoidalCategory.fst X' Z ≫ transportSrc e f := by
  subst X'
  simp [transportSrc]

theorem transportSrc_tensor_snd {X X' Z : V} (e : X = X') :
    transportSrc (congrArg (fun W => W ⊗ Z) e)
        (CartesianMonoidalCategory.snd X Z) =
      CartesianMonoidalCategory.snd X' Z := by
  subst X'
  simp [transportSrc]

theorem transportSrc_tensor_fst₂ {X X' Z Z' Y : V}
    (eX : X = X') (eZ : Z = Z') (f : X ⟶ Y) :
    transportSrc (congrArg₂ (fun W Q => W ⊗ Q) eX eZ)
        (CartesianMonoidalCategory.fst X Z ≫ f) =
      CartesianMonoidalCategory.fst X' Z' ≫ transportSrc eX f := by
  subst X'
  subst Z'
  simp [transportSrc]

theorem transportSrc_tensor_snd₂ {X X' Z Z' : V}
    (eX : X = X') (eZ : Z = Z') :
    transportSrc (congrArg₂ (fun W Q => W ⊗ Q) eX eZ)
        (CartesianMonoidalCategory.snd X Z) =
      CartesianMonoidalCategory.snd X' Z' ≫
        transportSrc eZ (𝟙 Z) := by
  subst X'
  subst Z'
  simp [transportSrc]

theorem transportSrc_tensor_snd₂_comp {X X' Z Z' Y : V}
    (eX : X = X') (eZ : Z = Z') (f : Z ⟶ Y) :
    transportSrc (congrArg₂ (fun W Q => W ⊗ Q) eX eZ)
        (CartesianMonoidalCategory.snd X Z ≫ f) =
      CartesianMonoidalCategory.snd X' Z' ≫ transportSrc eZ f := by
  subst X'
  subst Z'
  simp [transportSrc]

def ctxObjEq (Γ : LambdaIter.Ctx ν τ) :
    ctxObj (TypeModel.ofIter M) Γ =
      LambdaIter.Subtyping.Semantics.Categorical.ctxObj M Γ :=
  match Γ with
  | .nil => rfl
  | .snoc Γ _ A => congrArg (fun X => X ⊗ M.obj A) (ctxObjEq Γ)

@[simp] theorem ctxObj_ofIter (Γ : LambdaIter.Ctx ν τ) :
    ctxObj (TypeModel.ofIter M) Γ =
      LambdaIter.Subtyping.Semantics.Categorical.ctxObj M Γ := ctxObjEq (M := M) Γ

def boundObjEq : {n : Nat} → (β : LambdaSeq.LocallyNameless.BoundCtx τ n) →
    boundObj (TypeModel.ofIter M) β =
      LambdaIter.Subtyping.Semantics.Categorical.boundObj M β
  | 0, .nil => rfl
  | _ + 1, .snoc β A =>
      congrArg (fun X => X ⊗ M.obj A) (boundObjEq β)

@[simp] theorem boundObj_ofIter {n : Nat}
    (β : LambdaSeq.LocallyNameless.BoundCtx τ n) :
    boundObj (TypeModel.ofIter M) β =
      LambdaIter.Subtyping.Semantics.Categorical.boundObj M β := boundObjEq (M := M) β

@[simp] theorem envObj_ofIter (Γ : LambdaIter.Ctx ν τ) {n : Nat}
    (β : LambdaSeq.LocallyNameless.BoundCtx τ n) :
    envObj (TypeModel.ofIter M) Γ β =
      LambdaIter.Subtyping.Semantics.Categorical.envObj M Γ β := by
  simp only [envObj, LambdaIter.Subtyping.Semantics.Categorical.envObj,
    ctxObj_ofIter, boundObj_ofIter]

def envObjEq (Γ : LambdaIter.Ctx ν τ) {n : Nat}
    (β : LambdaSeq.LocallyNameless.BoundCtx τ n) :
    envObj (TypeModel.ofIter M) Γ β =
      LambdaIter.Subtyping.Semantics.Categorical.envObj M Γ β :=
  congrArg₂ (fun X Y => X ⊗ Y) (ctxObjEq (M := M) Γ) (boundObjEq (M := M) β)

theorem ctxLookup_ofIter [DecidableEq ν] {Γ : LambdaIter.Ctx ν τ}
    (x : ν) {A : τ} (h : Γ.lookup x = some A) :
    transportSrc (ctxObjEq (M := M) Γ) (ctxLookup (TypeModel.ofIter M) x h) =
      LambdaIter.Subtyping.Semantics.Categorical.ctxLookup M x h := by
  induction Γ with
  | nil => simp [LambdaIter.Ctx.lookup] at h
  | snoc Γ name B ih =>
      cases name with
      | none =>
          have h' : Γ.lookup x = some A := by
            simpa [LambdaIter.Ctx.lookup] using h
          unfold ctxLookup LambdaIter.Subtyping.Semantics.Categorical.ctxLookup ctxObjEq
          change transportSrc
              (congrArg (fun X => X ⊗ M.obj B) (ctxObjEq (M := M) Γ))
              (CartesianMonoidalCategory.fst _ _ ≫ ctxLookup (TypeModel.ofIter M) x h') =
            CartesianMonoidalCategory.fst _ _ ≫
              LambdaIter.Subtyping.Semantics.Categorical.ctxLookup M x h'
          rw [transportSrc_tensor_fst (ctxObjEq (M := M) Γ)]
          congr 1
          exact ih h'
      | some y =>
          by_cases hxy : x = y
          · subst y
            have hBA : B = A := by simpa [LambdaIter.Ctx.lookup] using h
            subst A
            unfold ctxLookup LambdaIter.Subtyping.Semantics.Categorical.ctxLookup ctxObjEq
            simp only [dif_pos rfl]
            exact transportSrc_tensor_snd (ctxObjEq (M := M) Γ)
          · unfold ctxLookup LambdaIter.Subtyping.Semantics.Categorical.ctxLookup ctxObjEq
            simp only [dif_neg hxy]
            have h' : Γ.lookup x = some A := by
              simpa [LambdaIter.Ctx.lookup, hxy] using h
            change transportSrc
                (congrArg (fun X => X ⊗ M.obj B) (ctxObjEq (M := M) Γ))
                (CartesianMonoidalCategory.fst _ _ ≫ ctxLookup (TypeModel.ofIter M) x h') =
              CartesianMonoidalCategory.fst _ _ ≫
                LambdaIter.Subtyping.Semantics.Categorical.ctxLookup M x h'
            rw [transportSrc_tensor_fst (ctxObjEq (M := M) Γ)]
            congr 1
            exact ih h'

theorem boundLookup_ofIter {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n} (i : Fin n) :
    transportSrc (boundObjEq (M := M) β)
        (boundLookup (TypeModel.ofIter M) (β := β) i) =
      LambdaIter.Subtyping.Semantics.Categorical.boundLookup M (β := β) i := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change transportSrc
            (congrArg (fun X => X ⊗ M.obj A) (boundObjEq (M := M) β))
            (CartesianMonoidalCategory.snd _ _) = CartesianMonoidalCategory.snd _ _
        exact transportSrc_tensor_snd (boundObjEq (M := M) β)
      · change transportSrc
            (congrArg (fun X => X ⊗ M.obj A) (boundObjEq (M := M) β))
            (CartesianMonoidalCategory.fst _ _ ≫ boundLookup (TypeModel.ofIter M) j) =
          CartesianMonoidalCategory.fst _ _ ≫
            LambdaIter.Subtyping.Semantics.Categorical.boundLookup M j
        rw [transportSrc_tensor_fst (boundObjEq (M := M) β)]
        congr 1
        exact ih j

theorem freeLookup_ofIter [DecidableEq ν] {Γ : LambdaIter.Ctx ν τ}
    {n : Nat} {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    (x : ν) {A : τ} (h : Γ.lookup x = some A) :
    transportSrc (envObjEq M Γ β)
        (freeLookup (TypeModel.ofIter M) (β := β) x h) =
      LambdaIter.Subtyping.Semantics.Categorical.freeLookup M (β := β) x h := by
  unfold freeLookup LambdaIter.Subtyping.Semantics.Categorical.freeLookup envObjEq
  change transportSrc
      (congrArg₂ (fun X Y => X ⊗ Y) (ctxObjEq (M := M) Γ) (boundObjEq (M := M) β))
      (CartesianMonoidalCategory.fst _ _ ≫ ctxLookup (TypeModel.ofIter M) x h) =
    CartesianMonoidalCategory.fst _ _ ≫
      LambdaIter.Subtyping.Semantics.Categorical.ctxLookup M x h
  rw [transportSrc_tensor_fst₂ (ctxObjEq (M := M) Γ) (boundObjEq (M := M) β)
    (ctxLookup (TypeModel.ofIter M) x h)]
  congr 1
  exact ctxLookup_ofIter M x h

theorem boundVar_ofIter {Γ : LambdaIter.Ctx ν τ}
    {n : Nat} {β : LambdaSeq.LocallyNameless.BoundCtx τ n} (i : Fin n) :
    transportSrc (envObjEq M Γ β)
        (boundVar (TypeModel.ofIter M) (Γ := Γ) i) =
      LambdaIter.Subtyping.Semantics.Categorical.boundVar M (Γ := Γ) i := by
  unfold boundVar LambdaIter.Subtyping.Semantics.Categorical.boundVar envObjEq
  change transportSrc
      (congrArg₂ (fun X Y => X ⊗ Y) (ctxObjEq (M := M) Γ) (boundObjEq (M := M) β))
      (CartesianMonoidalCategory.snd _ _ ≫ boundLookup (TypeModel.ofIter M) i) =
    CartesianMonoidalCategory.snd _ _ ≫
      LambdaIter.Subtyping.Semantics.Categorical.boundLookup M i
  rw [transportSrc_tensor_snd₂_comp (ctxObjEq (M := M) Γ) (boundObjEq (M := M) β)
    (boundLookup (TypeModel.ofIter M) i)]
  congr 1
  exact boundLookup_ofIter M i

end IterRestriction

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

namespace Isotope.LambdaSeq.Semantics.Categorical.Chosen

open CategoryTheory CategoryTheory.Limits

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : LambdaIter.Subtyping.Semantics.Categorical.TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type*} [LambdaIter.HasTy Φ τ]
  [LambdaIter.Subtyping.Semantics.Categorical.InstructionModel J M Φ]

/-- Chosen categorical semantics for exact lambda-seq, using its canonical
exact inclusion witness in lambda-iter. -/
noncomputable def denote {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaSeq.LocallyNameless.HasType Φ Γ β t A) :=
  LambdaIter.LocallyNameless.Categorical.denote J M h.embedIter

theorem denote_embedIter {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaSeq.LocallyNameless.HasType Φ Γ β t A) :
    LambdaIter.LocallyNameless.Categorical.denote J M h.embedIter = denote J M h := rfl

theorem denote_independent
    [LambdaIter.LocallyNameless.Categorical.TypingCoherent
      (ν := ν) (Φ := Φ) J M]
    {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaSeq.LocallyNameless.HasType Φ Γ β t A)
    (k : LambdaIter.LocallyNameless.HasType Φ Γ β t.embedIter A) :
    LambdaIter.LocallyNameless.Categorical.denote J M k = denote J M h :=
  LambdaIter.LocallyNameless.Categorical.TypingCoherent.denote_eq k h.embedIter

end Isotope.LambdaSeq.Semantics.Categorical.Chosen

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

namespace Isotope.LambdaSeq.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : LambdaIter.Subtyping.Semantics.Categorical.TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type*} [LambdaIter.HasTy Φ τ]
  [LambdaIter.Subtyping.Semantics.Categorical.InstructionModel J M Φ]

private theorem transportSrc_map {X X' Y : V} (e : X = X') (f : X ⟶ Y) :
    Isotope.LambdaSeq.Semantics.Categorical.transportSrc (congrArg J.obj e) (J.map f) =
      J.map (Isotope.LambdaSeq.Semantics.Categorical.transportSrc e f) := by
  subst X'
  simp [Isotope.LambdaSeq.Semantics.Categorical.transportSrc]

private theorem transportSrc_comp {X X' Y Z : C} (e : X = X')
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Isotope.LambdaSeq.Semantics.Categorical.transportSrc e (f ≫ g) =
      Isotope.LambdaSeq.Semantics.Categorical.transportSrc e f ≫ g := by
  subst X'
  simp [Isotope.LambdaSeq.Semantics.Categorical.transportSrc]

private theorem heq_of_transportSrc_eq {X X' Y : C} (e : X = X')
    (f : X ⟶ Y) (g : X' ⟶ Y)
    (h : Isotope.LambdaSeq.Semantics.Categorical.transportSrc e f = g) : HEq f g := by
  subst X'
  simpa [Isotope.LambdaSeq.Semantics.Categorical.transportSrc] using h

private theorem transportSrc_bind {R R' A B : V} (e : R = R')
    (f : J.obj R ⟶ J.obj A) (g : J.obj (R ⊗ A) ⟶ J.obj B) :
    Isotope.LambdaSeq.Semantics.Categorical.transportSrc (congrArg J.obj e)
        (LambdaIter.Subtyping.Semantics.Categorical.bind J f g) =
      LambdaIter.Subtyping.Semantics.Categorical.bind J
        (Isotope.LambdaSeq.Semantics.Categorical.transportSrc (congrArg J.obj e) f)
        (Isotope.LambdaSeq.Semantics.Categorical.transportSrc
          (congrArg J.obj (congrArg (fun X => X ⊗ A) e)) g) := by
  subst R'
  simp [Isotope.LambdaSeq.Semantics.Categorical.transportSrc]

private theorem transportSrc_envSnoc {X X' Y Y' A B : V}
    (eX : X = X') (eY : Y = Y') (f : J.obj (X ⊗ (Y ⊗ A)) ⟶ J.obj B) :
    Isotope.LambdaSeq.Semantics.Categorical.transportSrc
        (congrArg J.obj (congrArg (fun R => R ⊗ A)
          (congrArg₂ (fun P Q => P ⊗ Q) eX eY)))
        (J.map (α_ X Y A).hom ≫ f) =
      J.map (α_ X' Y' A).hom ≫
        Isotope.LambdaSeq.Semantics.Categorical.transportSrc
          (congrArg J.obj (congrArg₂ (fun P Q => P ⊗ (Q ⊗ A)) eX eY)) f := by
  subst X'
  subst Y'
  simp [Isotope.LambdaSeq.Semantics.Categorical.transportSrc]

/-- The independent proof-relevant lambda-seq denotation, specialized by
restriction of a lambda-iter model. -/
noncomputable def denoteOfIter {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaSeq.Subtyping.LocallyNameless.HasType Φ Γ β t A) :=
  letI := Isotope.LambdaSeq.Semantics.Categorical.InstructionModel.ofIter
    (τ := τ) (Φ := Φ) J M
  denote J (Isotope.LambdaSeq.Semantics.Categorical.TypeModel.ofIter M) h

/-- After identifying the independently constructed environment object with
the lambda-iter environment object, the two denotations are equal. -/
theorem denoteOfIter_transport_eq
    {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaSeq.Subtyping.LocallyNameless.HasType Φ Γ β t A) :
    Isotope.LambdaSeq.Semantics.Categorical.transportSrc
        (congrArg J.obj (Isotope.LambdaSeq.Semantics.Categorical.envObjEq M Γ β))
        (denoteOfIter J M h) =
      LambdaIter.Subtyping.Semantics.Categorical.denote J M h.embedIter := by
  letI := Isotope.LambdaSeq.Semantics.Categorical.InstructionModel.ofIter
    (τ := τ) (Φ := Φ) J M
  induction h with
  | fv h =>
      simp only [LambdaSeq.Subtyping.LocallyNameless.HasType.embedIter,
        LambdaSeq.Subtyping.LocallyNameless.HasType.embedCase,
        LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold denoteOfIter denote LambdaIter.Subtyping.Semantics.Categorical.denote
      rw [transportSrc_map (J := J)
        (Isotope.LambdaSeq.Semantics.Categorical.envObjEq M _ _)
        (Isotope.LambdaSeq.Semantics.Categorical.freeLookup
          (Isotope.LambdaSeq.Semantics.Categorical.TypeModel.ofIter M) _ h)]
      exact congrArg J.map
        (Isotope.LambdaSeq.Semantics.Categorical.freeLookup_ofIter M _ h)
  | bv =>
      simp only [LambdaSeq.Subtyping.LocallyNameless.HasType.embedIter,
        LambdaSeq.Subtyping.LocallyNameless.HasType.embedCase,
        LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold denoteOfIter denote LambdaIter.Subtyping.Semantics.Categorical.denote
      rw [transportSrc_map (J := J)
        (Isotope.LambdaSeq.Semantics.Categorical.envObjEq M _ _)
        (Isotope.LambdaSeq.Semantics.Categorical.boundVar
          (Isotope.LambdaSeq.Semantics.Categorical.TypeModel.ofIter M) _)]
      exact congrArg J.map
        (Isotope.LambdaSeq.Semantics.Categorical.boundVar_ofIter M _)
  | op ha ih =>
      simp only [LambdaSeq.Subtyping.LocallyNameless.HasType.embedIter,
        LambdaSeq.Subtyping.LocallyNameless.HasType.embedCase,
        LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold denoteOfIter denote LambdaIter.Subtyping.Semantics.Categorical.denote
      unfold denoteOfIter at ih
      rw [transportSrc_comp, ih]
      simp only [LambdaSeq.Subtyping.LocallyNameless.HasType.embedIter]
      unfold Isotope.LambdaSeq.Semantics.Categorical.InstructionModel.ofIter
      rfl
  | sub ha _ ih =>
      simp only [LambdaSeq.Subtyping.LocallyNameless.HasType.embedIter,
        LambdaSeq.Subtyping.LocallyNameless.HasType.embedCase,
        LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold denoteOfIter denote LambdaIter.Subtyping.Semantics.Categorical.denote
      unfold denoteOfIter at ih
      rw [transportSrc_comp, ih]
      simp only [LambdaSeq.Subtyping.LocallyNameless.HasType.embedIter]
      unfold Isotope.LambdaSeq.Semantics.Categorical.TypeModel.ofIter
      rfl
  | let₁ ha hb iha ihb =>
      simp only [LambdaSeq.Subtyping.LocallyNameless.HasType.embedIter,
        LambdaSeq.Subtyping.LocallyNameless.HasType.embedCase,
        LambdaCase.Subtyping.LocallyNameless.HasType.embed]
      unfold denoteOfIter denote LambdaIter.Subtyping.Semantics.Categorical.denote
      unfold denoteOfIter at iha ihb
      rw [transportSrc_bind, iha]
      congr 1
      · unfold Isotope.LambdaSeq.Semantics.Categorical.envSnocIso
          LambdaIter.Subtyping.Semantics.Categorical.envSnocIso
        change Isotope.LambdaSeq.Semantics.Categorical.transportSrc
            (congrArg J.obj (congrArg (fun R => R ⊗ M.obj _)
              (congrArg₂ (fun P Q => P ⊗ Q)
                (Isotope.LambdaSeq.Semantics.Categorical.ctxObjEq (M := M) Γ)
                (Isotope.LambdaSeq.Semantics.Categorical.boundObjEq (M := M) _))))
            (J.map (α_
              (Isotope.LambdaSeq.Semantics.Categorical.ctxObj
                (Isotope.LambdaSeq.Semantics.Categorical.TypeModel.ofIter M) Γ)
              (Isotope.LambdaSeq.Semantics.Categorical.boundObj
                (Isotope.LambdaSeq.Semantics.Categorical.TypeModel.ofIter M) _)
              (M.obj _)).hom ≫
                denote J (Isotope.LambdaSeq.Semantics.Categorical.TypeModel.ofIter M) hb) =
          J.map (α_ (LambdaIter.Subtyping.Semantics.Categorical.ctxObj M Γ)
              (LambdaIter.Subtyping.Semantics.Categorical.boundObj M _)
              (M.obj _)).hom ≫
            LambdaIter.Subtyping.Semantics.Categorical.denote J M hb.embedCase.embed
        rw [transportSrc_envSnoc (J := J)
          (Isotope.LambdaSeq.Semantics.Categorical.ctxObjEq (M := M) _)
          (Isotope.LambdaSeq.Semantics.Categorical.boundObjEq (M := M) _)]
        congr 1
      · exact Isotope.LambdaSeq.Semantics.Categorical.envObjEq M _ _

/-- Independent lambda-seq semantics and the chosen lambda-iter semantics
agree after the canonical object transport induced by model restriction. -/
theorem denoteOfIter_eq
    {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaSeq.Subtyping.LocallyNameless.HasType Φ Γ β t A) :
    HEq (denoteOfIter J M h)
      (LambdaIter.Subtyping.Semantics.Categorical.denote J M h.embedIter) :=
  by
    exact heq_of_transportSrc_eq
      (congrArg J.obj (Isotope.LambdaSeq.Semantics.Categorical.envObjEq M Γ β))
      (denoteOfIter J M h)
      (LambdaIter.Subtyping.Semantics.Categorical.denote J M h.embedIter)
      (denoteOfIter_transport_eq J M h)

end Isotope.LambdaSeq.Subtyping.Semantics.Categorical
