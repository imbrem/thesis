import Isotope.LambdaIter.Signature
import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of lambda-iter signatures

A *signature* bundles everything the raw syntax and its exact (subtyping-free)
typing judgment are parameterized by: a type universe with its four type
formers, an instruction set with source/target types and effect annotations,
and a designated pure effect.  This file makes that bundle first class and
gives it a category structure.

## Design notes, and what is deliberately absent

* **No `Subtyping` component.**  The exact typing judgment
  `Isotope.LambdaIter.LocallyNameless.HasType` has no `sub` constructor, so
  the unrefined development never consults a `Subtyping` instance.  Carrying
  one here would force every coherence law of a morphism to cross a transport
  in a `Type`-valued family (`Subty` is proof relevant), for no gain on the
  unrefined branch.  This is a scope decision, not an oversight: signature
  morphisms in the sense of this file say nothing about subtyping.
* **Strict preservation.**  A morphism preserves the type formers *on the
  nose*.  Weak (up-to-isomorphism) preservation is not even expressible: a
  bare type universe carries no notion of isomorphism, and the only candidate
  — mutual subtyping — is exactly what was dropped above.  The cost is that a
  map implementing the object-language `unit` by a distinguished base type is
  *not* a signature morphism; such a thing is a model, not a signature map.
* **Effects vary.**  `Eff` and `pureEff` are components, and a morphism sends
  the source's pure effect to the target's.  Purity therefore transports
  forwards along a morphism (`Sig.Hom.isPure`), which is what an action on the
  equational theory needs.  Keeping the effect set fixed would make the empty
  signature non-initial, since a fixed two-element effect lattice admits more
  than one bottom-preserving self-map.
-/

namespace Isotope.LambdaIter

universe u

/-- A lambda-iter signature: a type universe with its four type formers, an
instruction set with typing and effect annotations, and a designated pure
effect.  This is precisely the data the exact typing judgment and the
equational theory are parameterized by, with the deliberate omission of a
`Subtyping` structure (see the module docstring). -/
structure Sig : Type (u + 1) where
  /-- The object-language type universe. -/
  Ty : Type u
  /-- Its tensor, unit, coproduct and empty type. -/
  formers : TypeFormers Ty
  /-- The primitive instructions. -/
  Instr : Type u
  /-- The effect annotations. -/
  Eff : Type u
  /-- The distinguished effect witnessing purity. -/
  pureEff : Eff
  /-- Source and target types of each instruction. -/
  hasTy : HasTy Instr Ty
  /-- The effect of each instruction. -/
  hasEff : HasEff Instr Eff

namespace Sig

attribute [instance 100] Sig.formers Sig.hasTy Sig.hasEff

variable {S T U V : Sig.{u}}

/-- A signature morphism: a map of type universes strictly preserving the four
type formers, a map of instructions preserving source, target and effect, and
a map of effects preserving purity. -/
structure Hom (S T : Sig.{u}) : Type u where
  /-- Action on types. -/
  ty : S.Ty → T.Ty
  /-- Action on instructions. -/
  instr : S.Instr → T.Instr
  /-- Action on effects. -/
  eff : S.Eff → T.Eff
  /-- Tensor is preserved on the nose. -/
  ty_tensor : ∀ A B : S.Ty, ty (tensor A B) = tensor (ty A) (ty B)
  /-- The unit type is preserved on the nose. -/
  ty_unit : ty unit = unit
  /-- Coproducts are preserved on the nose. -/
  ty_coprod : ∀ A B : S.Ty, ty (coprod A B) = coprod (ty A) (ty B)
  /-- The empty type is preserved on the nose. -/
  ty_empty : ty empty = empty
  /-- Instruction sources are preserved. -/
  instr_src : ∀ f : S.Instr, instrSrc (instr f) = ty (instrSrc f)
  /-- Instruction targets are preserved. -/
  instr_trg : ∀ f : S.Instr, instrTrg (instr f) = ty (instrTrg f)
  /-- Instruction effects are preserved. -/
  instr_eff : ∀ f : S.Instr, instrEff (instr f) = eff (instrEff f)
  /-- The pure effect is preserved. -/
  eff_pure : eff S.pureEff = T.pureEff

namespace Hom

/-- Two signature morphisms agree as soon as their three carrier maps do: the
remaining fields are propositions. -/
@[ext] theorem ext {F G : Hom S T} (hty : F.ty = G.ty)
    (hinstr : F.instr = G.instr) (heff : F.eff = G.eff) : F = G := by
  cases F; cases G; cases hty; cases hinstr; cases heff; rfl

/-- The identity signature morphism. -/
@[simps] def id (S : Sig.{u}) : Hom S S where
  ty := _root_.id
  instr := _root_.id
  eff := _root_.id
  ty_tensor _ _ := rfl
  ty_unit := rfl
  ty_coprod _ _ := rfl
  ty_empty := rfl
  instr_src _ := rfl
  instr_trg _ := rfl
  instr_eff _ := rfl
  eff_pure := rfl

/-- Composition of signature morphisms, componentwise. -/
@[simps] def comp (F : Hom S T) (G : Hom T U) : Hom S U where
  ty := G.ty ∘ F.ty
  instr := G.instr ∘ F.instr
  eff := G.eff ∘ F.eff
  ty_tensor A B := by simp [F.ty_tensor, G.ty_tensor]
  ty_unit := by simp [F.ty_unit, G.ty_unit]
  ty_coprod A B := by simp [F.ty_coprod, G.ty_coprod]
  ty_empty := by simp [F.ty_empty, G.ty_empty]
  instr_src f := by simp [G.instr_src, F.instr_src]
  instr_trg f := by simp [G.instr_trg, F.instr_trg]
  instr_eff f := by simp [G.instr_eff, F.instr_eff]
  eff_pure := by simp [F.eff_pure, G.eff_pure]

/-- Purity transports forwards along a signature morphism.  This is the fact
an action on the equational theory needs: the `letBeta` and `uniformity`
side conditions are purity assumptions. -/
theorem isPure (F : Hom S T) {f : S.Instr} (h : IsPure S.pureEff f) :
    IsPure T.pureEff (F.instr f) := by
  unfold IsPure at h ⊢
  rw [F.instr_eff, h, F.eff_pure]

end Hom

/-- Signatures and their strict morphisms form a category.  All three laws
hold by `rfl`, since every component of a morphism is an ordinary function
and composition is function composition. -/
instance instCategory : CategoryTheory.Category.{u, u + 1} Sig.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_ty (S : Sig.{u}) : (CategoryTheory.CategoryStruct.id S).ty = _root_.id := rfl
@[simp] theorem id_instr (S : Sig.{u}) :
    (CategoryTheory.CategoryStruct.id S).instr = _root_.id := rfl
@[simp] theorem id_eff (S : Sig.{u}) :
    (CategoryTheory.CategoryStruct.id S).eff = _root_.id := rfl

@[simp] theorem comp_ty (F : S ⟶ T) (G : T ⟶ U) :
    (CategoryTheory.CategoryStruct.comp F G).ty = G.ty ∘ F.ty := rfl
@[simp] theorem comp_instr (F : S ⟶ T) (G : T ⟶ U) :
    (CategoryTheory.CategoryStruct.comp F G).instr = G.instr ∘ F.instr := rfl
@[simp] theorem comp_eff (F : S ⟶ T) (G : T ⟶ U) :
    (CategoryTheory.CategoryStruct.comp F G).eff = G.eff ∘ F.eff := rfl

end Sig

end Isotope.LambdaIter
