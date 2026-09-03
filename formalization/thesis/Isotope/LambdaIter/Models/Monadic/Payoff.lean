import Isotope.LambdaIter.Models.Monadic.Havoc
import Isotope.LambdaIter.Models.Initial

/-!
# Initiality, instantiated

`Syn S` is the initial algebra of the lambda-iter presentation
(`Models/Initial.lean`).  Combined with the concrete algebras of
`Models/Monadic/Concrete.lean` and `Models/Monadic/Havoc.lean`, that
statement acquires content: there is exactly one interpretation of the
syntax in the partiality monad, exactly one in the powerset, and the
comparison morphism between them is forced to be the graph map.

## The payoff

The last section separates a *pair of closed terms* using a model rather
than the syntactic quotient, and does so in a way no earlier example could:

```
let x = havoc () in ⟨x, x⟩        versus        ⟨havoc (), havoc ()⟩
```

In the powerset model the first denotes the *diagonal* of `(1 ⊕ 1) × (1 ⊕ 1)`
and the second denotes everything, so the lambda-iter theory does **not**
identify them (`not_eqv_havoc_dup`).  In a deterministic `Part` model of the
same signature the two are equal (`havocPart_dup_eq`).  So the separation is
genuinely a property of the chosen model, not of the syntax, and the two
algebras are provably distinct as interpretations of the same signature.

This is exactly the semantic shadow of the effect annotation: were `havoc`
declared pure, `letBeta` would prove the two terms equal outright, and
`Signature/Havoc.lean`'s `havocPure_not_isTotal` says no model could then
refute it.
-/

namespace Isotope.LambdaIter.Monadic

open LocallyNameless
open Isotope.Elgot
open CategoryTheory
open Isotope.LambdaIter.Monadic.SeqModel

/-! ### The unique morphisms out of the syntax -/

/-- **The denotation of lambda-iter in the partiality monad**, as the unique
morphism out of the initial algebra. -/
noncomputable def synToPart : Syn Sig.empty.{0} ⟶ partAlg := Syn.toHom _

/-- **The denotation of lambda-iter in the powerset**, likewise. -/
noncomputable def synToSet : Syn Sig.empty.{0} ⟶ setAlg := Syn.toHom _

/-- **The denotation of lambda-iter over the havoc signature in the
powerset.** -/
noncomputable def synToHavocSet : Syn Sig.havoc ⟶ havocSetAlg := Syn.toHom _

/-- There is no other morphism into the partiality algebra. -/
theorem synToPart_unique (F : Syn Sig.empty.{0} ⟶ partAlg) : F = synToPart :=
  Syn.hom_eq_toHom _ F

/-- There is no other morphism into the powerset algebra. -/
theorem synToSet_unique (F : Syn Sig.empty.{0} ⟶ setAlg) : F = synToSet :=
  Syn.hom_eq_toHom _ F

/-- There is no other morphism into the havoc powerset algebra. -/
theorem synToHavocSet_unique (F : Syn Sig.havoc ⟶ havocSetAlg) : F = synToHavocSet :=
  Syn.hom_eq_toHom _ F

/-- **Initiality forces the comparison triangle.**  The partial denotation
followed by the graph map *is* the powerset denotation -- not because the two
were defined compatibly, but because there is only one morphism out of the
syntax. -/
theorem synToPart_comp_partToSet : synToPart ≫ partToSetAlgHom = synToSet :=
  Syn.hom_eq_toHom _ _

/-- The concrete form of the previous theorem: the graph of the partial
denotation of a closed term is its powerset denotation. -/
theorem toSet_denote {A : Sig.empty.{0}.Ty} {t : Tm Empty Sig.empty.{0}.Instr 0}
    (h : HasType Sig.empty.{0}.Instr Ctx.nil BoundCtx.nil t A) :
    Part.toSet (denote (freeModel Part) h PUnit.unit) =
      denote (freeModel SetM) h PUnit.unit :=
  freeAlgHom_denote Part.toSetHom h

/-! ### A term pair separated by a real model

`havoc ()` at the boolean type, duplicated in two ways. -/

/-- Invoking `havoc`. -/
abbrev havocTm : Tm Empty Sig.havoc.Instr 0 := .op HavocInstr.havoc .unit

/-- The typing derivation of `havoc ()`. -/
abbrev havocDeriv : HasType Sig.havoc.Instr (Ctx.nil : Ctx Empty Sig.havoc.Ty)
    BoundCtx.nil havocTm EmptyTy.boolTy := .op .unit

/-- `let x = havoc () in ⟨x, x⟩`: one coin flip, used twice. -/
abbrev dupLet : HasType Sig.havoc.Instr (Ctx.nil : Ctx Empty Sig.havoc.Ty)
    BoundCtx.nil (.let₁ havocTm (.pair (.bv 0) (.bv 0)))
    (tensor EmptyTy.boolTy EmptyTy.boolTy) :=
  .let₁ havocDeriv (.pair .bv .bv)

/-- `⟨havoc (), havoc ()⟩`: two coin flips. -/
abbrev dupPair : HasType Sig.havoc.Instr (Ctx.nil : Ctx Empty Sig.havoc.Ty)
    BoundCtx.nil (.pair havocTm havocTm)
    (tensor EmptyTy.boolTy EmptyTy.boolTy) :=
  .pair havocDeriv havocDeriv

section Cset

/-- The full countable set of booleans: the denotation of `havoc ()`. -/
def cUniv : Nondet.CSet (Unit ⊕ Unit) := ⟨Set.univ, Set.countable_univ⟩

@[simp] theorem mem_cUniv (x : Unit ⊕ Unit) : x ∈ cUniv := Set.mem_univ x

/-- In the countable-powerset model, `havoc ()` denotes the full set. -/
theorem denote_havoc_cset :
    denote havocCSetModel havocDeriv PUnit.unit = cUniv := by
  show ((pure () : Nondet.CSet Unit) >>= fun _ => cUniv) = _
  rw [pure_bind]

/-- The shared coin flip: one choice, copied. -/
theorem denote_dupLet_cset :
    denote havocCSetModel dupLet PUnit.unit = cUniv >>= fun x => pure (x, x) := by
  show ((pure () : Nondet.CSet Unit) >>= fun _ => cUniv) >>=
      (fun x => (pure x : Nondet.CSet (Unit ⊕ Unit)) >>= fun a =>
        (pure x : Nondet.CSet (Unit ⊕ Unit)) >>= fun b => pure (a, b)) = _
  rw [pure_bind]
  exact bind_congr fun x => by rw [pure_bind, pure_bind]

/-- The two coin flips: two independent choices. -/
theorem denote_dupPair_cset :
    denote havocCSetModel dupPair PUnit.unit =
      cUniv >>= fun a => cUniv >>= fun b => pure (a, b) := by
  show ((pure () : Nondet.CSet Unit) >>= fun _ => cUniv) >>=
      (fun a => ((pure () : Nondet.CSet Unit) >>= fun _ => cUniv) >>=
        fun b => pure (a, b)) = _
  rw [pure_bind]

/-- Two independent coin flips can disagree. -/
theorem mem_denote_dupPair :
    ((Sum.inl (), Sum.inr ()) : (Unit ⊕ Unit) × (Unit ⊕ Unit)) ∈
      (denote havocCSetModel dupPair PUnit.unit :
        Nondet.CSet ((Unit ⊕ Unit) × (Unit ⊕ Unit))) := by
  rw [denote_dupPair_cset]
  exact Nondet.CSet.mem_bind.mpr ⟨Sum.inl (), mem_cUniv _,
    Nondet.CSet.mem_bind.mpr ⟨Sum.inr (), mem_cUniv _, rfl⟩⟩

/-- A copied coin flip cannot. -/
theorem not_mem_denote_dupLet :
    ((Sum.inl (), Sum.inr ()) : (Unit ⊕ Unit) × (Unit ⊕ Unit)) ∉
      (denote havocCSetModel dupLet PUnit.unit :
        Nondet.CSet ((Unit ⊕ Unit) × (Unit ⊕ Unit))) := by
  rw [denote_dupLet_cset]
  intro hmem
  obtain ⟨x, -, hx⟩ := Nondet.CSet.mem_bind.mp hmem
  have hx' : ((Sum.inl (), Sum.inr ()) : (Unit ⊕ Unit) × (Unit ⊕ Unit)) = (x, x) :=
    Nondet.CSet.mem_pure.mp hx
  exact Sum.inl_ne_inr ((congrArg Prod.fst hx').trans (congrArg Prod.snd hx').symm)

/-- **The countable-powerset model separates the two terms.** -/
theorem denote_dup_ne_cset :
    denote havocCSetModel dupLet PUnit.unit ≠
      denote havocCSetModel dupPair PUnit.unit := fun h =>
  not_mem_denote_dupLet (h ▸ mem_denote_dupPair)

/-- **The lambda-iter theory does not let a nondeterministic choice be
duplicated.**  A model, not the syntactic quotient, is what refutes it. -/
theorem not_eqv_havoc_dup :
    ¬ Eqv (Φ := Sig.havoc.Instr) Sig.havoc.pureEff
      (Ctx.nil : Ctx Empty Sig.havoc.Ty) BoundCtx.nil
      (.let₁ havocTm (.pair (.bv 0) (.bv 0))) (.pair havocTm havocTm)
      (tensor EmptyTy.boolTy EmptyTy.boolTy) := by
  intro he
  have h := (Alg.ofModel havocCSetModel).sound dupLet dupPair he
  simp only [ofModel_denote] at h
  exact denote_dup_ne_cset (congrFun h PUnit.unit)

end Cset

section PartSide

/-- A deterministic model of the havoc signature in the partiality monad:
`havoc` always returns the left boolean.  By `part_not_isTotal` no `Part`
model can do better. -/
noncomputable def havocPartModel : Model.{0, 0} Sig.havoc Part :=
  havocModel Part (pure (Sum.inl ()))

/-- **In a deterministic model the two terms are equal.**  So the separation
above is a property of the *model*, not of the syntax: the powerset algebra
and this partiality algebra are genuinely different interpretations of the
same signature. -/
theorem denote_dup_eq_part :
    denote havocPartModel dupLet PUnit.unit =
      denote havocPartModel dupPair PUnit.unit := by
  show ((pure () : Part Unit) >>= fun _ => (pure (Sum.inl ()) : Part (Unit ⊕ Unit))) >>=
      (fun x => (pure x : Part (Unit ⊕ Unit)) >>= fun a =>
        (pure x : Part (Unit ⊕ Unit)) >>= fun b => pure (a, b)) =
    ((pure () : Part Unit) >>= fun _ => (pure (Sum.inl ()) : Part (Unit ⊕ Unit))) >>=
      (fun a => ((pure () : Part Unit) >>= fun _ =>
        (pure (Sum.inl ()) : Part (Unit ⊕ Unit))) >>= fun b => pure (a, b))
  simp only [pure_bind]

/-- The powerset denotation is the carrier of the countable-powerset
denotation -- another instance of a morphism of algebras commuting with
denotation. -/
theorem carrier_denote_havoc {A : Sig.havoc.Ty} {t : Tm Empty Sig.havoc.Instr 0}
    (h : HasType Sig.havoc.Instr Ctx.nil BoundCtx.nil t A) :
    (denote havocCSetModel h PUnit.unit).carrier = denote havocSetModel h PUnit.unit := by
  have := congrFun (havocCSetToSetAlgHom.map_denote h) PUnit.unit
  simp only [havocCSetToSetAlgHom, Alg.homOfReinterpret_map, havocCSetAlg,
    havocSetAlg, ofModel_denote] at this
  exact this

/-- **The powerset model separates the two terms too.**  It follows from the
countable case, since the carrier map is injective. -/
theorem denote_dup_ne_set :
    denote havocSetModel dupLet PUnit.unit ≠
      denote havocSetModel dupPair PUnit.unit := by
  intro h
  refine denote_dup_ne_cset (Nondet.CSet.carrier_injective ?_)
  rw [carrier_denote_havoc dupLet, carrier_denote_havoc dupPair, h]

end PartSide


/-! ### Reading the separation back through initiality -/

/-- **The initial algebra distinguishes the pair.**  Same content as
`not_eqv_havoc_dup`, read in `Syn`. -/
theorem syn_denote_dup_ne :
    (Syn Sig.havoc).denote dupLet ≠ (Syn Sig.havoc).denote dupPair := fun h =>
  not_eqv_havoc_dup (Syn.eqv_of_mk_eq (by rwa [Syn.denote_mk, Syn.denote_mk] at h))

/-- **What initiality buys, concretely.**  The unique morphism from the syntax
into the powerset havoc algebra sends the two syntactic classes to different
elements.  The morphism was not designed to do this: it is the only morphism
there is, and the separation is forced by the model. -/
theorem synToHavocSet_separates :
    synToHavocSet.map ((Syn Sig.havoc).denote dupLet) ≠
      synToHavocSet.map ((Syn Sig.havoc).denote dupPair) := by
  intro h
  rw [Alg.Hom.map_denote', Alg.Hom.map_denote'] at h
  have h' : denote havocSetModel dupLet = denote havocSetModel dupPair := by
    simpa only [havocSetAlg, ofModel_denote] using h
  exact denote_dup_ne_set (congrFun h' PUnit.unit)

end Isotope.LambdaIter.Monadic
