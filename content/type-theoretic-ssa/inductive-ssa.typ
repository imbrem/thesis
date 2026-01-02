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

#let fig-ty-grammar = figure(
  [
    #grid(
      align: left,
      columns: 2,
      gutter: (2em, 2em),
      bnf(
        Prod($A ∈ sty(ms("X"))$, {
          Or[$tybase(X)$][_base type_ $X ∈ ms("X")$]
          Or[$Σ lb("L")$][_Σ (coproduct)_]
          Or[$Π lb("T")$][_Π (product)_]
        }),
      ),
      bnf(
        Prod($lb("L") ∈ senum(sty(ms("X")))$, {
          Or[$·$][]
          Or[$lb("L"), lty(lb("l"), A)$][where $lb("l") ∉ lb("L")$]
        }),
        Prod($lb("T") ∈ sstruct(sty(ms("X")))$, {
          Or[$·$][]
          Or[$lb("T"), fty(lb("f"), A)$][where $lb("f") ∉ lb("T")$]
        }),
      ),
    )
    $
      A × B & := Π [A, B] & #h(3em) & mb(1) & := Π (·) \
      A + B & := Σ [A, B] &         & mb(0) & := Σ (·)
    $
    $
      Π [A_0,...,A_(n - 1)] & = Π_i A_i & := Π ( lb("p")_0 : A_0, ..., lb("p")_(n - 1) : A_(n - 1) ) \
      Σ [A_0,...,A_(n - 1)] & = Σ_i A_i &   := Σ ( lb("i")_0(A_0), ..., lb("i")_(n - 1)(A_(n - 1)) )
    $
    \
  ],
  caption: [
    Grammar for simple types $A ∈ sty(ms("X"))$ parametrized by base types $ms("X")$.
  ],
  kind: image,
);

#fig-ty-grammar <simple-ty-grammar>

Our type system supports _subtyping_ $A sle() B$,
where a term of type $A$ can be used in place of a term of type $B$.
We give the rules for subtyping in @ty-wk;
these state that we're allowed to:

- Permute the fields of a product or the variants of a coproduct.
  In particular, this means
  that

  We call such interchangeable types $A ≈ B$ _equivalent_, defining
  $
    A ≈ B := A sle() B ⊓ B sle() A
  $

- Coerce the empty type $tzero = Π (·)$ to any type $A$
  (using @twk-zero)

- Drop any _affine_ type $A$ to the unit type $tunit = Π (·)$
  (using @twk-unit)

Combined with congruence, this allows us to repeatedly:

- _Add_ variants to a coproduct:
  "either $A$ or $B$" is a subtype of "either $A$, $B$, or $C$"

- _Remove_ fields from a product:
  _if_ $B$ is _affine_, "both $A$ and $B$" is a subtype of "just $A$"

An _affine_ type is precisely a type which can be freely discarded.
A type which is not affine is called _relevant_;
values of such types must be used at least once when introduced.

In general, a typing discipline which restricts how often a type can be used is called
_substructural_. We can classify substructural types $A$ based on two orthogonal axes:
- Whether they can be _copied_ (are _idempotent_), or must be used _at most_ once (are _unique_).

  We might forbid copying a type when it represents a resource which can only be used once:
  for example,
  a unique pointer to an owned block of memory
  (in a language with pointer equality, cloning the memory yields a _different_ object,
  while copying the pointer violates uniqueness).

- Whether they can be _discarded_ (are _affine_),
  or must be used _at least_ once (are _relevant_).

  We might forbid discarding a type when it represents a resource that must be cleaned up:
  for example, a file handle which must be closed or a mutex guard which must be released.

A type which is _relevant_ and _unique_ is called _linear_ ; such types must be used _exactly_ once.
On the other hand, a type which is both _affine_ and _idempotent_ is called _cartesian_ ;
such types can be used any number of times, including zero
-- this is the default behavior in most programming languages.

This gives us a lattice of potential _usage obligations_ $u ∈ useset$ for types,
which we may identify with sets $u ⊆ ℕ$ of allowed usage counts, generated as follows:

#let fig-quant-lattice = figure(
  [
    #align(center + horizon, diagram(
      node-inset: 0.7em,
      // debug: 3,
      $
          & "cartesian:" tqint ≈ {0, 1, 2, ...} \
        "affine:" tqaff ≈ {0, 1} edge("ur", <-) //
          &                                           & "idem:" tqidm ≈ {1, 2, 3, ...} edge("ul", <-) \
          & tqlin ≈ {1} edge("ul", <-) edge("ur", <-)
        /*
        \
        dem(0) edge("uu", "--", stroke: cdem) //
        & dem(1) edge("u", "=", stroke: cdem) //
        & dem(2) edge("uu", "--", stroke: cdem) //
        & dem(3) edge("uul", "--", stroke: cdem) //
        & ... edge("uull", "--", stroke: cdem)
        */
      $,
    ))
    \
  ],
  caption: [
    Meet-semilattice of usage obligations under $kqwk$,
    going from "less defined/less restricted" to "more defined/more restricted"
    -- i.e. $u ⊑ u' <==> u' ⊆ u$ as sets.
  ],
)

#fig-quant-lattice

We assign each type $A$ _usage obligation_ $useobg(A) ∈ useset$, defined to be the meet of the
usage obligations of its constituent base types:
#eqn-set(
  $useobg(tybase(X)) := useobg(X)$,
  $useobg(Σ (lb("L"), lty(lb("l"), A))) := useobg(Σ lb("L")) ⊓ useobg(A)$,
  $useobg(tzero) = tqint$,
  $useobg(Π (lb("T"), fty(lb("f"), A))) := useobg(Π lb("T")) ⊓ useobg(A)$,
  $useobg(tunit) = tqint$,
)

#fig-r-twk <ty-wk>

We say that:
- $A$ is _affine_, written $urel(saff, A)$, if $useobg(A) ⊑ tqaff$
- $A$ is _idempotent_, written $urel(sidm, A)$, if $useobg(A) ⊑ tqidm$
- $A$ is _cartesian_, written $urel(scart, A)$, if it is both affine and idempotent
  -- i.e. $useobg(A) ⊑ tqint$

More formally, we define a _typing discipline_ as follows, where _weakening_, in the case of types,
corresponds to subtyping:

#let def-ty-disc = definition(name: "Typing Discipline")[
  We define a _typing discipline_ $ms("X")$ to consist of:
  - A set of _types_ $|ms("X")|$.
    Where doing so is unambiguous, we identify $ms("X")$ with its set of types.

  - A preorder $X sle() Y$ on base types, _weakening_.

    We say two types $X, Y$ are _equivalent_, written $X ≈ Y$, if $X sle() Y$ and $Y sle() X$.

  - For each type $X$, a _usage obligation_ $useobg(X)$, s.t. $X ≈ Y ==> useobg(X) = useobg(Y)$

  We say a type is _affine_, written $urel(saff, X)$, if $useobg(X) ⊑ tqaff$,
  _idempotent_, written $urel(sidm, X)$, if $useobg(X) ⊑ tqidm$,
  and _cartesian_, written $urel(scart, X)$, if it is both affine and idempotent.

  Likewise, we say a typing discipline is
  _affine_ if all types are affine,
  _idempotent_ if all types are idempotent,
  and _cartesian_ if all types are cartesian.
]

#def-ty-disc

#lemma[
  If $ms("X")$ is a typing discipline, then so is $sty(ms("X"))$ when equipped with:
  - weakening the subtyping relation defined by the rules in @ty-wk.
  - usage obligations defined inductively as above

  Moreover, $sty(ms("X"))$ is affine/idempotent/cartesian iff $ms("X")$ is.
]

Given a type system $ms("X")$, we define
- A _context_ $Γ ∈ sctx(ms("X"))$ to be a list of variable-type pairs $x : A$ where
  $A ∈ ms("X")$.

  Roughly speaking, a context $Γ$ describes the set of variables live on entry to a program
  fragment; hence, weakening on contexts, $Γ sle() Δ$, allows us to:
  - Permuting the variables in $Γ$
  - Dropping variables $x : A$ where $A$ is affine
  - Weakening variable types

  We define the _usage_ obligation of a context $Γ$
  as the meet of the usage obligations of its constituent types:

- A _cocontext_ $ms("L") ∈ slctx(ms("X"))$ to be a list of label-type pairs $lb("l")(A)$
  where $A ∈ ms("X")$.

  A cocontext $ms("L")$ describes the set of _targets_ a program fragment may jump to on exit,
  each annotated with its parameter type; hence, weakening on cocontexts, $ms("L") sle() ms("M")$,
  allows us to:
  - Permuting the labels in $ms("L")$
  - Adding new, unreachable labels $lb("l")(A)$
  - Weakening parameter types pointwise

  We define the _usage_ obligation of a cocontext $ms("L")$
  as the meet of the usage obligations of its constituent types:

- A _polycontext_ $cal("L") ∈ sdnf(ms("X"))$ to be a list of tuples $clty(lb("l"), Γ, A)$
  where $Γ ∈ sctx(ms("X"))$ and $A ∈ ms("X")$.

  A polycontext $cal("L")$ describes
  the set of _entry points_ or _exit points_ -- _ports_ -- of a control-flow graph,
  with each port $lb("l")$ associated with a context of live variables $Γ$ and a parameter $A$.

  Weakening on polycontexts, $cal("L") sle() cal("M")$ allows us to:
  - Permute the ports in $cal("L")$
  - Adding new, unreachable ports $clty(lb("l"), Γ, A)$
  - Weaken live variable contexts and parameters pointwise

We give a grammar for contexts, cocontexts, and polycontexts, along with typing rules,
in @ctx-grammar-wk.

#let r-ctxwk-nil = rule(
  name: "Π-nil",
  $urel(saff, Γ)$,
  $cwk(Γ, ·)$,
)
#let r-ctxwk-cons = rule(
  name: "Π-cons",
  $clbwk(Γ, Δ)$,
  $tywk(A, B)$,
  $cwk(#$Γ, x : A$, #$Δ, x : A$)$,
);
#let r-ctxwk-perm = rule(
  name: [Π-perm],
  $σ "perm"$,
  $cwk(Γ, Δ)$,
  $cwk(σ · Γ, Δ)$,
);

#let r-lbwk-nil = rule(
  name: "Σ-nil",
  $lbcwk(·, ms("K"))$,
)
#let r-lbwk-cons = rule(
  name: "Σ-cons",
  $lbcwk(ms("L"), ms("K"))$,
  $tywk(A, B)$,
  $cwk(#$ms("L"), lb("l")(A)$, #$ms("K"), lb("l")(B)$)$,
);
#let r-lbwk-perm = rule(
  name: "Σ-perm",
  $σ "perm"$,
  $lbcwk(ms("L"), ms("K"))$,
  $lbcwk(σ · ms("L"), ms("K"))$,
);

#let r-clwk-nil = rule(
  name: "ΣΠ-nil",
  $clbwk(·, cal("K"))$,
)
#let r-clwk-cons = rule(
  name: "ΣΠ-cons",
  $clbwk(cal("L"), cal("K"))$,
  $cwk(Γ, Δ)$,
  $tywk(A, B)$,
  $clbwk(#$cal("L"), clty(lb("l"), Γ, A)$, #$cal("K"), clty(lb("l"), Δ, B)$)$,
);
#let r-clwk-perm = rule(
  name: [ΣΠ-perm],
  $σ "perm"$,
  $clbwk(cal("L"), cal("K"))$,
  $clbwk(σ · cal("L"), cal("K"))$,
);

#figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 2em),
      bnf(
        Prod($Γ$, {
          Or[$·^⊗$][]
          Or[$Γ, x : A$][]
        }),
      ),
      bnf(
        Prod($ms("L")$, {
          Or[$·^⊕$][]
          Or[$ms("L"), lty(lb("l"), A)$][]
        }),
      ),
      bnf(
        Prod($cal("L")$, {
          Or[$·^(⊕ ⊗)$][]
          Or[$cal("L"), clty(lb("l"), Γ, A)$][]
        }),
      ),
    )
    \
    #rule-set(
      declare-rule(r-ctxwk-nil, label: <ctxwk-nil>),
      declare-rule(r-ctxwk-cons, label: <ctxwk-cons>),
      declare-rule(r-ctxwk-perm, label: <ctxwk-perm>),
      declare-rule(r-lbwk-nil, label: <lbwk-nil>),
      declare-rule(r-lbwk-cons, label: <lbwk-cons>),
      declare-rule(r-lbwk-perm, label: <lbwk-perm>),
      declare-rule(r-clwk-nil, label: <clwk-nil>),
      declare-rule(r-clwk-cons, label: <clwk-cons>),
      declare-rule(r-clwk-perm, label: <clwk-perm>),
    )
    \
    $
          useobg(·^⊗) & := tqint & #h(5em) //
                                     &&                 useobg(Γ, x : A) & := useobg(Γ) ⊓ useobg(A) \
          useobg(·^⊕) & := tqint &   && useobg(ms("L"), lty(lb("l"), A)) & := useobg(ms("L")) ⊓ useobg(A) \
      useobg(·^(⊕ ⊗)) & := tqint &   &&  useobg(cal("L"), lb("l")[Γ](A)) & := useobg(cal("L")) ⊓ useobg(Γ) ⊓ useobg(A) \
    $
    \
  ],
  kind: image,
  caption: [
    Grammar, typing rules, and usage obligations for contexts, cocontexts, and polynomials.
    When unambiguous, we drop the superscript from the empty list.
  ],
) <ctx-grammar-wk>

#lemma[
  If $ms("X")$ is a typing discipline, then so are
  $sctx(ms("X"))$, $slctx(ms("X"))$, and $sdnf(ms("X"))$
  when equipped with the weakening relations defined by the rules in @ctx-grammar-wk.

  Moreover,
  $sctx(ms("X"))$, $slctx(ms("X"))$, and $sdnf(ms("X"))$ are affine/idempotent/cartesian
  iff $ms("X")$ is.
]

#let field2ctx(T) = $ms("coe")(#T)$
#let var2lctx(L) = $ms("coe")(#L)$

#let ctx2field(Γ) = $ms("coe")(#Γ)$
#let lctx2var(L) = $ms("coe")(#L)$

- We may coerce a field list $lb("T") ∈ sstruct(sty(ms("T")))$ 
into a context $field2ctx(lb("T")) ∈ sctx(sty(ms("X")))$
  by induction:
  #eqn-set(
    $field2ctx(·) := ·^⊗$,
    $field2ctx(#$lb("T"), fty(lb("f"), A)$) := field2ctx(lb("T")), lb("f") : A$,
  )

  Likewise, for 
    $Γ ∈ sctx(sty(ms("X")))$, we may define the inverse coercion 
    $ctx2field(Γ) ∈ $ by induction:
  #eqn-set(
    $ctx2field(·^⊗) := ·$,
    $ctx2field(#$Γ, x : A$) := ctx2field(Γ), fty(x, A)$,
  )

  We drop both coercions when unambiguous.

- Given $Σ lb("L") ∈ sty(ms("X"))$,
  we may coerce the label list $lb("L")$ into a cocontext $var2lctx(lb("L")) ∈ slctx(sty(ms("X")))$
  by induction:
  #eqn-set(
    $var2lctx(·) := ·$,
    $var2lctx(#$lb("L"), lty(lb("l"), A)$) := var2lctx(lb("L")), lb("l")(A)$,
  )

  Likewise, we may define the inverse coercion $lctx2var(ms("L"))$ by induction:
  #eqn-set(
    $lctx2var(·) := ·$,
    $lctx2var(#$ms("L"), lb("l")(A)$) := lctx2var(ms("L")), lty(lb("l"), A)$,
  )

  We drop both coercions when unambiguous.

- Given $Γ ∈ sctx(ms("X"))$ and $ms("L") ∈ slctx(ms("X"))$, we may define their
  _distributed product_ $Γ csplat ms("L") ∈ sdnf(ms("X"))$
  by induction as follows:
  #eqn-set(
    $Γ csplat · := ·$,
    $Γ csplat (#$ms("L"), lb("l")(A)$) := Γ, clty(lb("l"), Γ, A)$,
  )

/*
In general, we say a map $f : ms("X") -> ms("Y")$ is a _typing discipline morphism_ if
- $f$ preserves weakening: if $X sle() Y$, then $f(X) sle() f(Y)$
- $f$ reduces usage obligations: $useobg(f(X)) ⊑ useobg(X)$


Recall that we say a preorder $ms("X")$
- has _upper binary joins_ if any $X, Y ∈ |ms("X")|$ with upper bound $X, Y sle() Z$
  have a join $X ⊔ Y$
- has _lower binary meets_ if any $X, Y ∈ |ms("X")|$ with lower bound $Z sle() X, Y$
  have a meet $X ⊓ Y$
- is a _near prelattice_ if it has both upper binary joins and lower binary meets
- is a _prelattice_ if it has binary joins and meets for all pairs $X, Y ∈ |ms("X")|$

Note that the latter two conditions are trivial when $ms("Y")$ is cartesian.
*/

= Expressions

#import "../rules/hasty.typ": *

#todo[We now want to give a type system for expressions in a _cartesian_ type system]

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
