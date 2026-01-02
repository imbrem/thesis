#import "../../syntax.typ": *
#import "../../todos.typ": *

#show: show-syntax

#context if (thesis-state.get)().is-standalone {
  set document(title: "Type-Theoretic SSA")
  title()
}

#todo[
  In this chapter we:
  1. Give a type-and-effect system for #iter-calc() and 
    SSA parametrized by a set of base types $ms("X")$
    - First we define a type system over types $ms("Ty")[ms("X")]$
    - Then we give typing rules for expressions and programs, _and_...
    - State some basic metatheory
  2. Give an _effect system_ for #iter-calc() and SSA
  2. Give a _refinement theory_ for #iter-calc() and SSA using our equational theory
    - Metatheory of refinement: weakening
]

= Types and Contexts

#import "../rules/types.typ": *

Both our expression calculus #iter-calc() and our SSA region calculus #gssa-calc() use a 
system of _simple types_ $A ∈ sty(ms("X"))$ parametrized by a set of _base types_ $X ∈ ms("X")$,
consisting of:

- Atomic types $tybase(X)$ drawn from $ms("X")$ ; 
  where it does not introduce ambiguity,
  we make the coercion $tybase((-)) : ms("X") -> sty(ms("X"))$ implicit.

- $n$-ary coproducts /*(_$Σ$-types_)*/ $Σ lb("L")$ with named variants $lty(lb("l"), A)$ and

- $n$-ary products /*(_$Π$-types_)*/ $Π lb("T")$ with named fields $lty(lb("f"), A)$,

We give a grammar for these in @simple-ty-grammar. This system is intentionally minimalistic:

- Anonymous $n$-ary products $Π [A_0,...,A_(n - 1)]$ 
  and coproducts  $Σ [A_0,...,A_(n - 1)]$ desugar to named products and coproducts with 
  distinguished labels $lb("p")_i, lb("i")_i$.

- The unit type and empty type are simply the (unique) $0$-ary product and coproduct:
  $tunit = Π (·)$ and $tzero = Σ (·)$ respectively.

#fig-ty-grammar <simple-ty-grammar>

#todo[
  Should we:
  - Explain _affine_ vs _relevant_ types right away, 
    and simplify to cartesian at the end of the section?
  - Simplify to cartesian throughout (and change definition to just "cartesian type system");
    _re define_ general type systems w/ cartesian type systems as a special case later?
  - Affine types are not _that_ complicated, and we can skim over relevant types as they're not 
    important till (much) later 
    (as context weakening only requires affinity, 
    and our simple type system is cartesian and so doesn't use splits)
  - The only issue is we want rules to determine a type affine (by trivial induction), 
    so might as well do relevant too or that's confusing
  - I guess it just takes up space but _cognitively_ it's not much 
    (a type is affine/relevant iff all its components are affine/relevant, recursively)
]

Our type system supports _subtyping_ $A sle() B$, where a term of type $A$ can be used in place of 
a term of type $B$. In particular, the subtyping relation allows us to:
- _Add_ variants to a coproduct: "either $A$ or $B$" is a subtype of "either $A$, $B$, or $C$"
  (using @twk-sigma)
- _Remove_ fields from a product: "both $A$ and $B$" is a subtype of "just $A$"
  (using @twk-pi)
- Coerce the empty type $tzero = Π (·)$ to any type $A$
  (using @twk-zero)
- Drop any type $A$ to the unit type $tunit = Π (·)$

This a _cartesian_ typing discipline, since we are allowed to freely discard and duplicate
values of any type. 
// Later: we'll consider more general _substructural_ typing disciplines where this is not the case.
We give rules for our subtyping relation in @cart-ty-wk; again, 
this is parametrized by a subtyping $X sle() Y$ on base types $X, Y ∈ ms("X")$.

#fig-r-twk <cart-ty-wk>

Our product types and coproduct types are _ordered_, but our subtyping discipline allows us to 
freely permute elements using the rules @twk-sigma-perm and @twk-pi-perm. In particular, this means
that different permutations of a sum or product are _interchangeable_ since, for example,
$Π lb("T") sle() Π (ρ · lb("T"))$ and
$Π (ρ · lb("L")) sle() Π (ρ^(-1) · ρ · lb("L")) = Π lb("L")$ for any permutation $ρ$.

We call such interchangeable types $A ≈ B$ _equivalent_, defining
$
  A ≈ B := A sle() B ⊓ B sle() A
$

More formally, we define a _typing discipline_ as follows, where _weakening_, in the case of types,
corresponds to subtyping:

#let def-ty-disc = definition(name: "Type Discipline")[
  We define a _typing discipline_ $ms("X")$ to consist of:
  - A set of _types_ $ms("X")$
  - A near-prelattice $X sle() Y$ on base types, _weakening_
  - An upper set $saff ⊆ X$ of _affine_ types
  - A lower set $srel ⊆ X$ of _relevant types_

  We say two types $X, Y$ are _equivalent_, written $X ≈ Y$, if $X sle() Y$ and $Y sle() X$.

  We say a typing discipline is _affine_ if $saff = X$, _relevant_ if $srel = X$, and
  _cartesian_ if it is both affine and relevant.
]

#def-ty-disc

Recall that a _near-prelattice_ is a preorder $sle()$ such that, for any $X, Y ∈ ms("X")$,
- If there exists a lower bound $Z sle() X, Y$, then there exists a _greatest_ such lower bound
  (a _meet_) s.t. $Z sle() X ⊓ Y sle() X, Y$ ; this is always unique up to equivalence.
- If there exists an upper bound $X, Y sle() Z$, then there exists a _least_ such upper bound
  (a _join_) s.t. $X, Y sle() X ⊔ Y sle() Z$ ; this is always unique up to equivalence.

We have that:

#lemma[
  If $ms("X")$ is a cartesian typing discipline, then so is $sty(ms("X"))$ when equipped with the
  subtyping relation defined by the rules in @cart-ty-wk.

  In particular,
  - $tybase(-) : ms("X") -> sty(ms("X"))$ is a _near-prelattice embedding_: 
    an injective map which preserves meets and joins while reflecting the order. 
  - $sty(ms("X"))$ is in fact a _bounded prelattice_: it has all finite meets and joins.
]

#todo[Should we add a figure for meets and joins in $sty(ms("X"))$ (up to equivalence)]

In general, we say a map $f : ms("X") -> ms("Y")$ is a _typing discipline morphism_ if
- $f$ preserves weakening: if $X sle() Y$, then $f(X) sle() f(Y)$
- $f$ preserves meets and joins:
  - if $X ⊓ Y$ exists, then $f(X ⊓ Y) = f(X) ⊓ f(Y)$
  - if $X ⊔ Y$ exists, then $f(X ⊔ Y) = f(X) ⊔ f(Y)$
- $f$ preserves affinity: if $X ∈ saff_ms("X")$, then $f(X) ∈ saff_ms("Y")$
- $f$ preserves relevance: if $X ∈ srel_ms("X")$, then $f(X) ∈ srel_ms("Y")$

Note that the latter two conditions are trivial when $ms("Y")$ is cartesian.

#todo[
  - An _INSERT NAME HERE_ type discipline has a _unit_ $tunit$ w/ $X sle() tunit$ iff $X ∈ saff$;
    this is _bounded above_ iff $saff = X$ (i.e. an _affine_ type system)
  - _Bounded below_ if $tzero sle() X$
]

= Expressions

#import "../rules/hasty.typ": *

#todo[introduce concept of a function space]

#todo[fix notation for function space judgement]

#fig-r-hasty

#todo[explain #op-calc(ms("F")), #case-calc(ms("F")) as sublanguages of #iter-calc(ms("F"))]

#todo[weakening]

#todo[substitution]

= Regions

#todo[introduce concept of an _expression space_]

#todo[fix notation for expression space judgement]

#import "../rules/haslb.typ": *

#fig-haslb-br

#todo[introduce concept of a _region space_]

#fig-haslb-ssa

#todo[weakening]

#todo[substitution]

#todo[SSA is just a region-space too... hence gSSA]

#fig-haslb-gssa

#todo[weakening]

#todo[substitution]

#todo[label-substitution]

= Effects

#todo[want to build an equational theory]

#todo[substitution is not good equationally]

#todo[want a notion of _effects_]

#todo[introduce _effect systems_]

== Expressions

#todo[introduce _direct_ effects (versus indirect, up to equivalence)]

#fig-r-eff-hasty

== Regions

#todo[introduce _effect labels_ for SSA]

#todo[rules...]

= Refinement

#todo[in fact, want a _refinement theory_]

#todo[(expression) basis ; refinement system _over_ $ms("E")$ ; order]

#todo[basic metatheory]

#todo[(region) basis ; refinement system _over_ $ms("E") ; ms("T")$ ; order embedding]

#todo[basic metatheory]