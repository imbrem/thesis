// Monadic (interaction-tree) semantics for λ_iter: notation and the semantic
// equations, as reusable `#let` definitions. Import into the chapter; nothing
// here renders on its own.
//
//   #import "/thesis/type-theoretic-ssa/lambda-iter/semantics.typ": *
//
// The semantics interprets every type as a set, every context as a product of
// sets, and every term-in-context Γ ⊢ a : A as a function ⟦Γ⟧ → ITree ⟦A⟧ into
// the interaction-tree monad (an Elgot monad). The presentation is the
// Kleisli reading of the categorical semantics; the category theory is the
// subject of the next chapter.

#import "/lib/prelude.typ": *

// ===========================================================================
//  Notation
// ===========================================================================

// Denotation brackets ⟦-⟧.
#let sem(x) = $lr(⟦ #x ⟧)$
// Nil (the unique unit value) as a denotable term.
#let lnil = $()$

// The interaction-tree monad over the fixed event signature of instructions I.
#let itree(a) = $sans("ITree") med #a$
// Interaction trees quotiented by weak bisimulation ≈ -- the type on which the
// Elgot-monad axioms hold strictly. The ≈ subscript distinguishes it cleanly
// from the raw `itree`.
#let qitree(a) = $attach(sans("ITree"), br: ≈) med #a$
// The quotient/lifting map ⌊-⌋ : ITree A → ITree_≈ A sending a raw tree to its
// bisimulation class.
#let qlift(t) = $lr(⌊ #t ⌋)$
// Interaction-tree constructors: return a value, a silent step, an event node.
#let iret(a) = $sans("Ret") med #a$
#let itau(t) = $sans("Tau") med #t$
#let ivis(e, k) = $sans("Vis") med #e med #k$
// Monadic return, and the Elgot iterate operator. Bind is written `≫=` inline.
#let kret(a) = $sans("ret") med #a$
#let kiter(f) = $sans("iterate") med #f$
// The unique map out of the empty set (used to interpret `abort`).
#let kabsurd = $sans("absurd")$

// ===========================================================================
//  Interaction-tree monad operations
// ===========================================================================

// return / bind (≫=, by cases on the head node) / the Elgot iterate operator.
#let itree-op-eqns = (
  $kret(a) = iret(a)$,
  $iret(a) ≫= k = k med a$,
  $itau(t) ≫= k = itau((t ≫= k))$,
  $ivis(e, c) ≫= k = ivis(e, (λ r. med c med r ≫= k))$,
  $kiter(f) med a
    = f med a ≫= λ v. med casex(v, b, kret(b), a', itau((kiter(f) med a')))$,
)

// ===========================================================================
//  Interpretation of types and contexts (as sets)
// ===========================================================================

#let sem-ty-eqns = (
  $sem(tyunit) = 1$,
  $sem(A tytensor B) = sem(A) × sem(B)$,
  $sem(tyempty) = ∅$,
  $sem(A tysum B) = sem(A) + sem(B)$,
)
#let sem-ctx-eqns = (
  $sem(·) = 1$,
  $lr(⟦ Γ, x : A ⟧) = sem(Γ) × sem(A)$,
)

// ===========================================================================
//  Interpretation of terms: ⟦Γ ⊢ a : A⟧ : ⟦Γ⟧ → ITree ⟦A⟧
// ===========================================================================
// One case per term former, following the typing rules. γ ∈ ⟦Γ⟧ is the
// environment; γ(x) looks a variable up; γ[x ↦ v] extends it.

#let sem-tm-eqns = (
  $sem(x) med γ = kret(γ(x))$,
  $sem(f med a) med γ = sem(a) med γ ≫= sem(f)$,
  $sem(letx(x, a, b)) med γ = sem(a) med γ ≫= λ v. med sem(b) med γ[x ↦ v]$,
  $sem(lnil) med γ = kret(lnil)$,
  $sem((a, b)) med γ
    = sem(a) med γ ≫= λ u. med sem(b) med γ ≫= λ v. med kret((u, v))$,
  $sem(letx((x, y), a, c)) med γ
    = sem(a) med γ ≫= λ (u, v). med sem(c) med γ[x ↦ u, y ↦ v]$,
  $sem(linl(a)) med γ = sem(a) med γ ≫= λ u. med kret((linl(u)))$,
  $sem(linr(b)) med γ = sem(b) med γ ≫= λ v. med kret((linr(v)))$,
  $sem(casex(e, x, a, y, b)) med γ
    = sem(e) med γ ≫= λ v. med casex(v, u, sem(a) med γ[x ↦ u], w, sem(b) med γ[y ↦ w])$,
  $sem(labort(a)) med γ = sem(a) med γ ≫= kabsurd$,
  $sem(iterx(a, x, b)) med γ = sem(a) med γ ≫= kiter((λ v. med sem(b) med γ[x ↦ v]))$,
)
