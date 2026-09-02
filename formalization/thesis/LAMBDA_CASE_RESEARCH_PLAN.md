# LambdaCase and LambdaSeq research plan

This note records proof boundaries and branch dependencies.  It is not a claim
that the listed completeness or representation results are already proved.

## Existing branch stack to reuse

- PR #35 (`formalization/lambda-iter-no-subtyping`) defines exact named and
  locally nameless typing without `Subtyping` or a `sub` constructor.
- PR #38 extends #35 with the complete no-subtyping LambdaIter theory.  Merged
  PR #43 is present in this branch and gives abstract categorical soundness,
  conditional on explicit model diagram interfaces.
- PRs #44 and #49 prove equality renaming and pure typed substitution.  The
  purity condition is essential: substituting an effectful term for a pure
  variable invalidates pure-let beta and uniformity.
- PR #48 derives bare categorical iteration diagrams, but intentionally leaves
  contextual syntax-to-combinator diagrams as model obligations.
- PR #34 supplies categorical subtyping coherence; PR #46 supplies named
  derivation semantics.  Neither should be duplicated in LambdaCase.

LambdaCase should be cut from the no-subtyping stack after it lands, by omitting
`iter` syntax and the iteration equation family.  LambdaSeq should then be a
second, parallel restriction omitting tensor destructuring, sums, and abort;
it should not be encoded using dummy coproduct structure.

## Completeness target

The clean primary statement is initiality, not faithfulness of one chosen Set
model.  Construct a syntactic distributive Freyd category `SynCase`:

1. Objects are object-language types (or contexts, with a proved strict
   context/type comparison).
2. Effectful arrows are exactly typed terms with one distinguished input,
   quotiented by LambdaCase equivalence.
3. Pure arrows are the quotient of syntactically pure terms.
4. Composition is `let`; tensorial strength is context extension; unit,
   tensor, finite coproducts, and distributivity are induced by the term
   constructors.
5. Prove all operations respect the quotient using weakening, pure typed
   substitution, and the commuting conversions.
6. Interpret the signature operations as generating effectful arrows.
7. For every signature-respecting distributive Freyd model, define the unique
   structure-preserving interpretation functor by recursion on typing.

The reification lemma says that interpreting a term in `SynCase` yields its own
equivalence class.  Consequently, equality in every model implies equality in
the syntactic model and hence derivability.  This proves completeness without
requiring a normal-form or decidability theorem.

Milestones that can compile independently:

- substitution and weakening for LambdaCase, preferably obtained by restriction
  of #44/#49 with explicit comparison theorems;
- quotient category and well-defined identity/composition;
- premonoidal/Freyd laws;
- coproduct/distributivity laws;
- interpretation and reification;
- initiality and the semantic-completeness corollary.

For LambdaSeq the same construction stops after the Freyd structure.  This is
the useful test that coproduct assumptions have not leaked into sequencing.

## No-subtyping variant

The current `LambdaIter.Subtyping` interface cannot express equality-only
subtyping: it requires witnesses `empty <= A` and `A <= unit`.  Therefore the
correct no-subtyping experiment is the separate exact judgment in #35, not an
`Eq` instance for the existing class.  Define LambdaCase and LambdaSeq by
restricting that syntax and prove embeddings into their larger exact theories.
Keep comparison with proof-relevant subtyping theorem-level: exact derivations
embed using reflexivity, and denotation agrees by `coe_refl`.

## Identity semantics

`Isotope.LambdaCase.Semantics.Identity` defines the direct Lean evaluator as
the generic monadic evaluator specialized to `Id`; their agreement is
definitional.  A later richer presentation can choose an inductive universe of
internal types and a recursive interpretation into Lean types, then instantiate
the existing `TypeModel` equivalences.

There is a sharp distinction about iteration:

- LambdaCase has an `Id` model because it asks only for `Monad Id`.
- `Iterate Id` itself is impossible on all Lean types: choose state `PUnit`,
  result `Empty`, and the body that always returns the recursive summand.
- Hence `Id` cannot have a `LawfulElgotMonad` instance either.  This is not just
  failure of a particular fixpoint law, and it assumes total iteration over a
  universe containing `Empty`.  Restricted guarded/finite iteration is a
  different interface.

## Non-Kleisli distributive Freyd model

A good small candidate is a genuinely premonoidal category of computations
whose tensor is not bifunctorial (for example, a stateful or process model with
an observational quotient), paired with its central pure subcategory.  Such a
model cannot be *equivalent as a premonoidal category* to the Kleisli category
of a **commutative** monad, whose tensor is monoidal.  This does not establish
the much stronger claim “not Kleisli-equivalent to any Set monad”: ordinary
noncommutative Set monads also yield genuinely premonoidal Kleisli categories.

For the stronger claim, the safest route is an invariant obstruction.  Any
Kleisli category of a Set monad has a right adjoint to its pure embedding and
is generated in the precise Kleisli-adjunction sense.  Construct a small
distributive Freyd category whose identity-on-objects pure functor has no right
adjoint; then it cannot arise from any Set monad.  Candidate finite categories
must be checked for finite coproducts, distributivity, centrality, and the
right-adjoint obstruction.  Until such a checked example is formalized, this
remains a research problem rather than a theorem.

## Commuting comparisons

Keep the desired square split into named theorems:

- syntax restriction followed by LambdaIter categorical interpretation equals
  direct LambdaCase categorical interpretation;
- the Kleisli distributive-Freyd interpretation equals the direct monadic
  evaluator;
- therefore the outer LambdaCase-to-LambdaIter-to-semantics diagram commutes.

Each proof should be induction on the typing derivation.  The second theorem
also needs coherence lemmas for context association, type interpretation
isomorphisms, and instruction arrows; PRs #34, #43, and #48 identify the
interfaces already available and the remaining contextual obligations.
