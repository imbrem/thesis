import Isotope.LambdaIter.Models.HomOver
import Isotope.LambdaIter.Models.Limits
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# The total category of signatures and models

`Total` is the category of pairs `(S, X)` with `S` a signature and `X` a model
of `S`; a morphism is a signature morphism `g` together with a map of models
over `g`.  This is the Grothendieck-style total category of the (contravariant)
family `S ↦ Alg S`, with its Hom defined **directly** rather than as
`Σ g, X ⟶ g* Y`.

## Why the Hom is defined directly

Reindexing a model along a signature morphism is only a *pseudo*functor in the
signature: `Alg.reindex (g ≫ h) Y` and `Alg.reindex g (Alg.reindex h Y)` have
carriers `Y.El (β.map (h.ty ∘ g.ty)) _` and `Y.El ((β.map g.ty).map h.ty) _`,
which are equal by `BoundCtx.map_comp` but **not** definitionally equal.  A
Grothendieck construction over a strict functor is therefore unavailable
without transporting along an equality of `Alg` records.  Defining the Hom
directly avoids all of that: composition needs only `BoundCtx.map_comp` at the
level of *elements*, which is exactly what `Alg.HomOver.comp` already does.

## What is in this file

* `Total`, `Total.Hom`, and `Category Total`.
* `Alg.homOverIdEquiv`: a map of models over `𝟙 S` is the same thing as a
  morphism of `Alg S`.  This is the fibre statement in its cleanest form.
* `Total.incl S : Alg S ⥤ Total`, the fibre inclusion, and the proof that it
  is faithful.
* `Total.fibreEquiv`: the morphisms of `Total` lying over `𝟙 S` are exactly
  the morphisms of `Alg S`.  **This is near-tautological by construction** —
  see its docstring.
* `Total.incl_not_full`: the fibre inclusion is *not* full, with an explicit
  witness.  This is the substantive neighbouring statement: it is what makes
  the fibred picture non-degenerate, and it is why the fibre statement above
  has to mention `𝟙` at all.
* `Total.isInitialOfFibrewise`: the Grothendieck initiality principle, reducing
  initiality in `Total` to initiality of the signature plus uniqueness of the
  map of models over the unique signature morphism.

## Honest boundary

No object of `Total` is shown to be initial here, because that needs a model
whose maps out are unique — the quotiented syntax, which this file does not
construct.  `Total.isInitialOfFibrewise` is exactly the interface such a
construction has to meet, and `Sig.uniqueFromEmpty` already discharges its
first hypothesis at the empty signature.
-/

namespace Isotope.LambdaIter

open LocallyNameless CategoryTheory

universe u w

/-! ### The unit and associativity laws for maps of models -/

namespace Alg

namespace HomOver

variable {S T U V : Sig.{u}} {X : Ops.{u, w} S} {Y : Ops.{u, w} T}
  {Z : Ops.{u, w} U} {W : Ops.{u, w} V} {g : S ⟶ T} {h : T ⟶ U} {k : U ⟶ V}

/-- The identity is a left unit for composition. -/
theorem id_comp (F : HomOver g X Y) : (HomOver.id X).comp F = F :=
  HomOver.ext fun {_n β _A} x =>
    (congrArg (Ops.tr Y (BoundCtx.map_comp (_root_.id) g.ty β).symm rfl)
        (F.map_tr (BoundCtx.map_id β).symm rfl x)).trans
      (Ops.tr_tr (X := Y) _ _ (BoundCtx.map_comp (_root_.id) g.ty β).symm rfl
        (F.map x))

/-- The identity is a right unit for composition. -/
theorem comp_id (F : HomOver g X Y) : F.comp (HomOver.id Y) = F :=
  HomOver.ext fun {_n β _A} x =>
    Ops.tr_tr (X := Y) (BoundCtx.map_id (BoundCtx.map g.ty β)).symm rfl
      (BoundCtx.map_comp g.ty (_root_.id) β).symm rfl (F.map x)

/-- Composition of maps of models is associative. -/
theorem assoc (F : HomOver g X Y) (G : HomOver h Y Z) (H : HomOver k Z W) :
    (F.comp G).comp H = F.comp (G.comp H) :=
  HomOver.ext fun {_n β _A} x =>
    ((congrArg (Ops.tr W (BoundCtx.map_comp (h.ty ∘ g.ty) k.ty β).symm rfl)
          (H.map_tr (BoundCtx.map_comp g.ty h.ty β).symm rfl
            (G.map (F.map x)))).trans
        (Ops.tr_tr (X := W) _ _ (BoundCtx.map_comp (h.ty ∘ g.ty) k.ty β).symm rfl
          (H.map (G.map (F.map x))))).trans
      (Ops.tr_tr (X := W) (BoundCtx.map_comp h.ty k.ty (BoundCtx.map g.ty β)).symm
        rfl (BoundCtx.map_comp g.ty (k.ty ∘ h.ty) β).symm rfl
        (H.map (G.map (F.map x)))).symm

end HomOver

/-! ### Maps over the identity are morphisms of models -/

variable {S : Sig.{u}}

/-- A map of models over `𝟙 S`, read as a morphism of `Alg S`. -/
def Hom.ofHomOver {X Y : Alg.{u, w} S}
    (F : HomOver (𝟙 S) X.toOps Y.toOps) : X ⟶ Y where
  map {_n β _A} x := Y.toOps.tr (BoundCtx.map_id β) rfl (F.map x)
  map_var i :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        ((F.map_var i).trans (Ops.heq_var Y.toOps (BoundCtx.map_id _) i)))
  map_op f a :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        ((F.map_op f a).trans
          (Ops.heq_op Y.toOps (BoundCtx.map_id _) f
            ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _).symm))))
  map_let₁ a b :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        ((F.map_let₁ a b).trans
          (Ops.heq_let₁ Y.toOps (BoundCtx.map_id _) rfl rfl
            (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm)))
  map_unit :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        (F.map_unit.trans (Ops.heq_unit Y.toOps (BoundCtx.map_id _))))
  map_pair a b :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        ((F.map_pair a b).trans
          (Ops.heq_pair Y.toOps (BoundCtx.map_id _) rfl rfl
            (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm)))
  map_let₂ a c :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        ((F.map_let₂ a c).trans
          (Ops.heq_let₂ Y.toOps (BoundCtx.map_id _) rfl rfl rfl
            ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _).symm)
            (Ops.tr_heq _ _ _ _).symm)))
  map_inl a :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        ((F.map_inl a).trans
          (Ops.heq_inl Y.toOps (BoundCtx.map_id _) rfl rfl
            (Ops.tr_heq _ _ _ _).symm)))
  map_inr b :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        ((F.map_inr b).trans
          (Ops.heq_inr Y.toOps (BoundCtx.map_id _) rfl rfl
            (Ops.tr_heq _ _ _ _).symm)))
  map_case e l r :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        ((F.map_case e l r).trans
          (Ops.heq_case Y.toOps (BoundCtx.map_id _) rfl rfl rfl
            ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _).symm)
            (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm)))
  map_abort a :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        ((F.map_abort a).trans
          (Ops.heq_abort Y.toOps (BoundCtx.map_id _) rfl
            ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _).symm))))
  map_iter a b :=
    eq_of_heq
      ((Ops.tr_heq _ _ _ _).trans
        ((F.map_iter a b).trans
          (Ops.heq_iter Y.toOps (BoundCtx.map_id _) rfl rfl
            (Ops.tr_heq _ _ _ _).symm
            ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _).symm))))

/-- A morphism of `Alg S`, read as a map of models over `𝟙 S`. -/
def Hom.toHomOver {X Y : Alg.{u, w} S} (G : X ⟶ Y) :
    HomOver (𝟙 S) X.toOps Y.toOps where
  map {_n β _A} x := Y.toOps.tr (BoundCtx.map_id β).symm rfl (G.map x)
  map_var i :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq (G.map_var i)).trans
        (Ops.heq_var Y.toOps (BoundCtx.map_id _).symm i))
  map_op f a :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq (G.map_op f a)).trans
        (Ops.heq_op Y.toOps (BoundCtx.map_id _).symm f
          ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm))
  map_let₁ a b :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq (G.map_let₁ a b)).trans
        (Ops.heq_let₁ Y.toOps (BoundCtx.map_id _).symm rfl rfl
          (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm))
  map_unit :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq G.map_unit).trans
        (Ops.heq_unit Y.toOps (BoundCtx.map_id _).symm))
  map_pair a b :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq (G.map_pair a b)).trans
        (Ops.heq_pair Y.toOps (BoundCtx.map_id _).symm rfl rfl
          (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm))
  map_let₂ a c :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq (G.map_let₂ a c)).trans
        (Ops.heq_let₂ Y.toOps (BoundCtx.map_id _).symm rfl rfl rfl
          ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm
          (Ops.tr_heq _ _ _ _).symm))
  map_inl a :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq (G.map_inl a)).trans
        (Ops.heq_inl Y.toOps (BoundCtx.map_id _).symm rfl rfl
          (Ops.tr_heq _ _ _ _).symm))
  map_inr b :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq (G.map_inr b)).trans
        (Ops.heq_inr Y.toOps (BoundCtx.map_id _).symm rfl rfl
          (Ops.tr_heq _ _ _ _).symm))
  map_case e l r :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq (G.map_case e l r)).trans
        (Ops.heq_case Y.toOps (BoundCtx.map_id _).symm rfl rfl rfl
          ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm
          (Ops.tr_heq _ _ _ _).symm (Ops.tr_heq _ _ _ _).symm))
  map_abort a :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq (G.map_abort a)).trans
        (Ops.heq_abort Y.toOps (BoundCtx.map_id _).symm rfl
          ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm))
  map_iter a b :=
    (Ops.tr_heq _ _ _ _).trans
      ((heq_of_eq (G.map_iter a b)).trans
        (Ops.heq_iter Y.toOps (BoundCtx.map_id _).symm rfl rfl
          (Ops.tr_heq _ _ _ _).symm
          ((Ops.tr_heq _ _ _ _).trans (Ops.tr_heq _ _ _ _)).symm))

@[simp] theorem Hom.ofHomOver_map {X Y : Alg.{u, w} S}
    (F : HomOver (𝟙 S) X.toOps Y.toOps) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} (x : X.El β A) :
    (Hom.ofHomOver F).map x = Y.toOps.tr (BoundCtx.map_id β) rfl (F.map x) :=
  rfl

@[simp] theorem Hom.toHomOver_map {X Y : Alg.{u, w} S} (G : X ⟶ Y) {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} (x : X.El β A) :
    (Hom.toHomOver G).map x =
      Y.toOps.tr (BoundCtx.map_id β).symm rfl (G.map x) := rfl

/-- **Maps of models over `𝟙 S` are exactly the morphisms of `Alg S`.**

The content is the transport along `BoundCtx.map_id`; the twelve laws match up
one for one, since `(𝟙 S).ty` is the identity function and every coherence
transport of `HomOver` is therefore a transport along `rfl`. -/
def homOverIdEquiv (X Y : Alg.{u, w} S) :
    HomOver (𝟙 S) X.toOps Y.toOps ≃ (X ⟶ Y) where
  toFun := Hom.ofHomOver
  invFun := Hom.toHomOver
  left_inv F :=
    HomOver.ext fun {_n β _A} x =>
      Ops.tr_tr (X := Y.toOps) (BoundCtx.map_id β) rfl
        (BoundCtx.map_id β).symm rfl (F.map x)
  right_inv G :=
    Alg.Hom.ext fun {_n β _A} x =>
      Ops.tr_tr (X := Y.toOps) (BoundCtx.map_id β).symm rfl
        (BoundCtx.map_id β) rfl (G.map x)

@[simp] theorem homOverIdEquiv_apply_map {X Y : Alg.{u, w} S}
    (F : HomOver (𝟙 S) X.toOps Y.toOps) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} (x : X.El β A) :
    (homOverIdEquiv X Y F).map x =
      Y.toOps.tr (BoundCtx.map_id β) rfl (F.map x) := rfl

@[simp] theorem homOverIdEquiv_symm_apply_map {X Y : Alg.{u, w} S} (G : X ⟶ Y)
    {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty} (x : X.El β A) :
    ((homOverIdEquiv X Y).symm G).map x =
      Y.toOps.tr (BoundCtx.map_id β).symm rfl (G.map x) := rfl

end Alg

/-! ### The total category -/

/-- An object of the total category: a signature together with a model of it. -/
structure Total : Type (max (u + 1) (w + 1)) where
  /-- The signature. -/
  sig : Sig.{u}
  /-- A model of it. -/
  alg : Alg.{u, w} sig

namespace Total

/-- A morphism of the total category: a signature morphism together with a map
of models over it. -/
structure Hom (P Q : Total.{u, w}) : Type (max u w) where
  /-- The action on signatures. -/
  sig : P.sig ⟶ Q.sig
  /-- The action on models, over `sig`. -/
  hom : Alg.HomOver sig P.alg.toOps Q.alg.toOps

namespace Hom

variable {P Q R T : Total.{u, w}}

/-- Two morphisms of the total category agree when their signature components
are equal and their model components are heterogeneously equal. -/
theorem ext' {F G : Hom P Q} (hs : F.sig = G.sig) (hh : HEq F.hom G.hom) :
    F = G := by
  cases F; cases G; cases hs; cases hh; rfl

/-- Equal morphisms have heterogeneously equal model components. -/
theorem heq_hom_of_eq {F G : Hom P Q} (e : F = G) : HEq F.hom G.hom := by
  cases e; rfl

/-- The identity morphism. -/
def id (P : Total.{u, w}) : Hom P P := ⟨𝟙 P.sig, Alg.HomOver.id _⟩

/-- Composition. -/
def comp (F : Hom P Q) (G : Hom Q R) : Hom P R :=
  ⟨F.sig ≫ G.sig, F.hom.comp G.hom⟩

end Hom

/-- Pairs of a signature and a model of it form a category. -/
instance instCategory : Category.{max u w, max (u + 1) (w + 1)} Total.{u, w} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp F := Hom.ext' rfl (heq_of_eq (Alg.HomOver.id_comp F.hom))
  comp_id F := Hom.ext' rfl (heq_of_eq (Alg.HomOver.comp_id F.hom))
  assoc F G H := Hom.ext' rfl (heq_of_eq (Alg.HomOver.assoc F.hom G.hom H.hom))

@[simp] theorem id_sig (P : Total.{u, w}) :
    (CategoryStruct.id P).sig = 𝟙 P.sig := rfl

@[simp] theorem comp_sig {P Q R : Total.{u, w}} (F : P ⟶ Q) (G : Q ⟶ R) :
    (CategoryStruct.comp F G).sig = F.sig ≫ G.sig := rfl

end Total

/-! ### The fibre over a fixed signature -/

namespace Total

variable {S : Sig.{u}}

/-- The fibre inclusion of the models of a fixed signature into the total
category.  On morphisms it is `Alg.homOverIdEquiv` read backwards. -/
def incl (S : Sig.{u}) : Alg.{u, w} S ⥤ Total.{u, w} where
  obj X := ⟨S, X⟩
  map {X Y} F := ⟨𝟙 S, (Alg.homOverIdEquiv X Y).symm F⟩
  map_id _X := Hom.ext' rfl (heq_of_eq (Alg.HomOver.ext fun _ => rfl))
  map_comp {_X _Y Z} F G :=
    Hom.ext' rfl
      (heq_of_eq
        (Alg.HomOver.ext fun {_n β _A} x =>
          Alg.Ops.eq_tr_of_heq (BoundCtx.map_id β).symm rfl
            (((Alg.Ops.tr_heq Z.toOps
                    (BoundCtx.map_comp (_root_.id) (_root_.id) β).symm rfl _).trans
                (((Alg.Ops.tr_heq Z.toOps
                        (BoundCtx.map_id
                          (BoundCtx.map (_root_.id) β)).symm rfl _).trans
                    (heq_of_eq
                      (Alg.Hom.map_tr G (BoundCtx.map_id β).symm rfl
                        (F.map x)))).trans
                  (Alg.Ops.tr_heq Z.toOps (BoundCtx.map_id β).symm rfl
                    (G.map (F.map x))))).symm)))

@[simp] theorem incl_obj (X : Alg.{u, w} S) : (incl S).obj X = ⟨S, X⟩ := rfl

@[simp] theorem incl_map_sig {X Y : Alg.{u, w} S} (F : X ⟶ Y) :
    ((incl S).map F).sig = 𝟙 S := rfl

/-- **The fibre inclusion is faithful.** -/
instance inclFaithful : (incl.{u, w} S).Faithful where
  map_injective {X Y} {_F _G} e :=
    (Alg.homOverIdEquiv X Y).symm.injective (eq_of_heq (Hom.heq_hom_of_eq e))

/-- **The morphisms of the total category lying over `𝟙 S` are exactly the
morphisms of `Alg S`.**

This is the statement the author asked for, and it is *near-tautological by
construction*: the fibre is **defined** as the morphisms whose signature
component is `𝟙 S`, so nothing is being discovered.  Its whole Lean content is
`BoundCtx.map_id` and the cancellation of the resulting transport on the round
trips, packaged in `Alg.homOverIdEquiv`.

The substantive neighbouring statements are `inclFaithful` above and
`incl_not_full` below. -/
def fibreEquiv (X Y : Alg.{u, w} S) :
    {F : (⟨S, X⟩ : Total.{u, w}) ⟶ ⟨S, Y⟩ // F.sig = 𝟙 S} ≃ (X ⟶ Y) where
  toFun F := Alg.homOverIdEquiv X Y (F.2 ▸ F.1.hom)
  invFun G := ⟨(incl S).map G, rfl⟩
  left_inv := by
    rintro ⟨⟨g, hm⟩, (rfl : g = 𝟙 S)⟩
    simp [incl, Equiv.symm_apply_apply]
  right_inv G := by simp [incl, Equiv.apply_symm_apply]

end Total

/-! ### The fibre inclusion is not full -/

namespace Total

open Alg

/-- The unique map of terminal models over the effect-collapsing endomorphism
of the null signature.  Everything is a singleton, so there is nothing to
check. -/
def nullTwist :
    HomOver Sig.collapseNullEff (Alg.terminal.{0, 0} Sig.ofNull).toOps
      (Alg.terminal.{0, 0} Sig.ofNull).toOps where
  map _ := PUnit.unit
  map_var _ := HEq.rfl
  map_op _ _ := HEq.rfl
  map_let₁ _ _ := HEq.rfl
  map_unit := HEq.rfl
  map_pair _ _ := HEq.rfl
  map_let₂ _ _ := HEq.rfl
  map_inl _ := HEq.rfl
  map_inr _ := HEq.rfl
  map_case _ _ _ := HEq.rfl
  map_abort _ := HEq.rfl
  map_iter _ _ := HEq.rfl

/-- A morphism of the total category between two objects of the *same* fibre
that does not lie over the identity. -/
def nullTwistHom :
    (⟨Sig.ofNull, Alg.terminal.{0, 0} Sig.ofNull⟩ : Total.{0, 0}) ⟶
      ⟨Sig.ofNull, Alg.terminal.{0, 0} Sig.ofNull⟩ :=
  ⟨Sig.collapseNullEff, nullTwist⟩

/-- **The fibre inclusion is not full.**  A morphism of the total category
between two objects of the same fibre may move the signature, so `incl` misses
morphisms; this is what makes the fibred picture non-degenerate, and it is why
`fibreEquiv` has to restrict to the morphisms over `𝟙`. -/
theorem incl_not_full :
    ¬ ∀ H : (incl.{0, 0} Sig.ofNull).obj (Alg.terminal Sig.ofNull) ⟶
        (incl Sig.ofNull).obj (Alg.terminal Sig.ofNull),
      ∃ F : Alg.terminal.{0, 0} Sig.ofNull ⟶ Alg.terminal Sig.ofNull,
        (incl Sig.ofNull).map F = H := by
  intro hfull
  obtain ⟨F, hF⟩ := hfull nullTwistHom
  exact Sig.collapseNullEff_ne_id
    (congrArg (fun H : (⟨Sig.ofNull, Alg.terminal.{0, 0} Sig.ofNull⟩ : Total.{0, 0}) ⟶
      ⟨Sig.ofNull, Alg.terminal Sig.ofNull⟩ => H.sig) hF).symm

end Total

/-! ### The Grothendieck initiality principle -/

namespace Total

/-- **Initiality in the total category reduces to initiality of the signature
plus uniqueness of the map of models over the unique signature morphism.**

This is the interface a construction of the quotiented syntax has to meet:
`Sig.uniqueFromEmpty` already discharges the first hypothesis at
`Sig.empty`, and the second is exactly the statement that the syntax over a
fixed signature admits a unique interpretation in every model — reindexed
along the unique signature morphism.

No object of `Total` is shown to be initial in this file: that needs a model
whose maps out are unique, i.e. the quotiented syntax, which is not built
here. -/
def isInitialOfFibrewise (P : Total.{u, w})
    (hsig : ∀ T : Sig.{u}, Unique (P.sig ⟶ T))
    (halg : ∀ (Q : Total.{u, w}) (g : P.sig ⟶ Q.sig),
      Unique (Alg.HomOver g P.alg.toOps Q.alg.toOps)) :
    Limits.IsInitial P :=
  letI : ∀ Q : Total.{u, w}, Unique (P ⟶ Q) := fun Q =>
    { default := ⟨(hsig Q.sig).default, (halg Q (hsig Q.sig).default).default⟩
      uniq := fun F => by
        obtain ⟨g, hm⟩ := F
        have hg : g = (hsig Q.sig).default := (hsig Q.sig).uniq g
        subst hg
        exact Hom.ext' rfl (heq_of_eq ((halg Q _).uniq hm)) }
  Limits.IsInitial.ofUnique P

end Total

end Isotope.LambdaIter
