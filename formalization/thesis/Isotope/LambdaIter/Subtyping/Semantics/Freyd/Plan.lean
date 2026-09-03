import Isotope.LambdaIter.Subtyping.Semantics.IterationDiagrams
import Isotope.LambdaIter.Semantics.Soundness

/-!
# The general Freyd route: axiom-to-obligation map

This module is the *plan* for instantiating
`LambdaIter.LocallyNameless.Categorical.TypingCoherent` and
`LambdaIter.LocallyNameless.Categorical.LawfulModel` over an **arbitrary**
`StrongElgotFreydCategory J : V ⥤ C`, rather than over a Kleisli category.
It contains no declarations: it records, ahead of the proofs, exactly which
categorical law each syntactic axiom scheme reduces to, and which auxiliary
lemmas the reduction needs.  Every entry marked *closed* below is discharged by
a named theorem in a sibling module of this directory; every entry marked
*open* is an honest boundary.

## 0. The setting

Fixed throughout: a cartesian symmetric `V` with finite coproducts and
`DistributiveTensor`, a symmetric premonoidal `C` with finite coproducts,
`DistributivePremonoidalCategory`, `Iteration` and `ElgotCategory`, and
`J : V ⥤ C` with `[StrongElgotFreydCategory J]`; a
`Subtyping.Semantics.Categorical.TypeModel τ V` called `M`, and an
`InstructionModel J M Φ`.  The denotation under analysis is
`Subtyping.Semantics.Categorical.denote J M`, and the coercion-free denotation
`LocallyNameless.Categorical.denote J M h` is that applied to `h.toGeneric`.

Three *derived* pieces of structure are used constantly and are worth naming:

* **centrality of values**: `FreydCategory.image_central J f` says `J.map f` is
  central, so `J.map f ⋉ g = J.map f ⋊ g`.  This is what makes an environment
  reshuffle commute past an arbitrary computation, and it is the only exchange
  law available.
* **strength of the tensor isomorphism**:
  `Functor.StrongPremonoidal.tensorIso`, together with its two one-variable
  naturality fields, is what lets `extend`/`bind` be reassociated at all.
* **the distributor** `DistributiveTensor.leftIso` and the inverse coproduct
  comparison `splitMapCoprod J = inv (coprodComparison J)`, which exist because
  `DistributiveFreydCategory` asks `J` to preserve finite coproducts.

## 1. The combinator algebra (the enabling layer)

None of the syntactic axioms can be attacked directly.  They all reduce first
to equations between the five combinators of
`Subtyping/Semantics/Categorical.lean` — `extend`, `bind`, `pair`,
`caseWithContext`, `abort`, `contextualLoop` — and these need their own algebra
first.  The four families are:

| family | statement shape | needs |
|---|---|---|
| **unit/eta** | `extend J f ≫ J.map (snd _ _) = f` | strong premonoidal coherence only |
| **naturality in the environment** | `J.map p ≫ bind J f g = bind J (J.map p ≫ f) (J.map (p ⊗ₘ 𝟙) ≫ g)` | centrality of `J.map p` |
| **naturality in the value** | `bind J (f ≫ J.map q) g = bind J f (J.map (𝟙 ⊗ₘ q) ≫ g)` | one-variable naturality of `tensorIso` |
| **associativity** | `bind J (bind J f g) k = bind J f (bind J (…) (…))` | centrality plus the associator |

`pair`, `caseWithContext` and `contextualLoop` are *defined* through `bind`, so
each inherits the first three families; only `contextualLoop`'s environment
naturality is not inherited, because it must move a pure map across `iterate`.
That one is a genuine use of `ElgotFreydCategory.uniformity`
(`loop_pure_uniformity`), preceded by `ElgotCategory.naturality` to make the two
loops share an exit object.

*Status*: `Freyd/Combinators.lean` (unit/eta, both naturalities, purity of
`pair` on value morphisms), `Freyd/Iteration.lean` (the `contextualLoop`
laws).

## 2. Environment renaming (the substitution layer)

`Tm.lift`, `Tm.underBinder`, `Tm.underTwoBinders` and `Tm.instantiate` appear in
thirteen of the nineteen schemes.  Monadically these are handled by
`Subtyping/Semantics/Substitution.lean` (`denote_rename`, `denote_bsubst`,
`denote_instantiate`, 380 lines); categorically the corresponding statement is
a *naturality theorem for the whole environment construction*:

> for a `TypedRenaming β β'` there is a value morphism
> `pullHom r : envObj M Γ β' ⟶ envObj M Γ β`, and
> `denote J M (h.rename r) = J.map (pullHom r) ≫ denote J M h`.

Its proof is a structural induction on the derivation in which every step is
exactly one instance of "naturality in the environment" from §1.  It is the
single largest missing artifact of the general route, and it is what makes the
sequencing and iteration schemes statable at all.

*Status*: `Freyd/Rename.lean`.

## 3. Purity factorisation

`letBeta` and `uniformity` quantify over a *syntactically pure* subterm.  The
obligation is the converse of what `EffectModel` supplies:

> if `Pure pureEff t` and `h : HasType Φ Γ β t A` then there is a value
> morphism `v : envObj M Γ β ⟶ M.obj A` with `denote J M h = J.map v`.

The base case is exactly `Categorical.PureInstructionModel`
(`LambdaIter/Semantics/Categorical.lean:39`).  The inductive cases need §1's
purity lemmas: `bind J (J.map u) (J.map w) = J.map (lift (𝟙) u ≫ w)`,
`pair J (J.map u) (J.map w) = J.map (lift u w)`, and the corresponding
`caseWithContext` clause, which is where the *general* route pays a real price:
a pure scrutinee must be split by the value-category coproduct before the
distributor is applied.  `abort` is pure because `M.emptyIsInitial.to` is a
value morphism, and `iter` is excluded from `Pure` by design.

*Status*: **open**.  See §7.

## 4. Structural axioms (`LawfulModel.structural`, nine schemes)

| scheme | reduces to | needs |
|---|---|---|
| `letEta` | `extend J f ≫ J.map (snd _ _) = f` | §1 unit/eta |
| `unitEta` | the same, plus `M.unitIso.hom = toUnit` (uniqueness in cartesian `V`) | §1 unit/eta |
| `caseBetaL` | `caseWithContext J (f ≫ J.map coprod.inl) l r = bind J f l` | distributor + `pureBinaryCofanIsColimit` |
| `caseBetaR` | its mirror image | as above |
| `caseEta` | `caseWithContext J f (J.map (snd ≫ inl)) (J.map (snd ≫ inr)) = f` | distributor + coproduct extensionality |
| `pairEta` | `bind J f (J.map (lift (snd ≫ fst) (snd ≫ snd))) = f` | §1 unit/eta and §1 purity of `pair` |
| `emptyInitial` | `bind J (abort J M z) g = bind J (abort J M z) g'` | `TensorEmptyStrict` (see §6) |
| `pairBeta` | reassociation of two nested `bind`s | §1 associativity **and** §2 (`Tm.lift`) |
| `letBeta` | `bind J (J.map v) g = J.map (lift (𝟙) v) ≫ g` | §3 **and** a categorical `denote_instantiate` |

*Status*: the first seven are `Freyd/Structural.lean`; `pairBeta` needs §2;
`letBeta` needs §3 and is the single hardest obligation of the whole route.

## 5. Sequencing axioms (`LawfulModel.sequencing`, six schemes)

All six are commuting conversions.  Each is one instance of `bind`
associativity from §1 together with §2 to account for the `underBinder`
weakening on the continuation; `bindLetCase` additionally commutes `bind` past
`caseWithContext`, and `bindPair`/`bindLetPair` past the `envPairHom`
reassociation.  No axiom beyond the Freyd structure and distributivity is
needed: in particular no iteration law and no purity.

*Status*: gated on §2.

## 6. Iteration axioms (`LawfulModel.contextualIteration`, four schemes)

| scheme | categorical law | wrapping needed |
|---|---|---|
| `fixpoint` | `ElgotCategory.fixpoint` | `contextualLoop` unfolds to a `caseWithContext` on the body |
| `naturality` | `ElgotCategory.naturality` | absorb a `bind` continuation into the exit branch |
| `codiagonal` | `ElgotCategory.codiagonal` | flatten a nested `contextualLoop`; needs §2 twice |
| `iterBind` | definitional after §1 | `bind`/`contextualLoop` interchange |

`IterationDiagrams.lean` states the four *bare* laws; every entry in the
"wrapping" column is the work that file explicitly does not do.  The
environment-threading is supplied by `StrongElgotFreydCategory.strength`.

`LawfulModel.uniformity` is separate: it is `ElgotFreydCategory.uniformity`
preceded by §3 (to turn the pure step term `h` into a value morphism) and §2
(to interpret `Tm.underBinder`/`Tm.instantiate` in the commuting square).

## 7. The two genuinely missing categorical laws

1. **Nullary distributivity.** `DistributiveTensor` asks only that `X ⊗ -`
   preserve *binary* coproducts, which does not imply `R ⊗ 0 ≅ 0`.  The missing
   law is already declared, as `LambdaSSA.Semantics.Categorical.TensorEmptyStrict`,
   with no instance anywhere.  It is what kills the `abort` slack in
   `TypingCoherent` and validates `emptyInitial`.

2. **Purity factorisation** (§3).  `EffectModel` deliberately gives only the
   `J.map f`-implies-pure direction; the converse holds when the effect
   relation is taken to be `J.imageProperty`.

## 8. Typing coherence

`TypingCoherent` is *not* an axiom-soundness statement: it is
derivation-independence.  Under `[InjectiveFormers τ]` every intermediate type
in a derivation is determined by the term and its result type **except** for
the slack introduced by `abort`, which types at every result type.  The
categorical induction hypothesis is therefore a disjunction, not a span:

> for `h : HasType Γ β t A` and `k : HasType Γ β t A'`, either `A = A'` and the
> two denotations agree, or **both** factor through `J.obj (M.obj empty)`.

`FactorsThroughEmpty`, `FactorsThroughEmpty.comp` and
`FactorsThroughEmpty.eq_of_prefix` (`LambdaSSA/Semantics/Empty.lean`) are the
propagation lemmas; the `bind` case needs `TensorEmptyStrict` and the `iter`
case needs `ElgotCategory.fixpoint`.  No parametricity or logical relation is
required — this is strictly simpler than the monadic `Coupling.lean`
development, which needs a `VRel` span because `Type`-valued models cannot see
that an empty-typed prefix is initial.
-/
