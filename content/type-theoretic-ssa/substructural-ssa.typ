#import "../../syntax.typ": *
#import "../../todos.typ": *

#show: show-syntax

#context if (thesis-state.get)().is-standalone {
  set document(title: "Substructural SSA")
  title()
}

#todo[From the top now!]

= Type and Effect System

== Types and Contexts

#import "../rules/types.typ": *

#todo[Note: same set of types as before]

#todo[Segue into this ; move a bit into preface]

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

We say that:
- $A$ is _affine_, written $urel(saff, A)$, if $useobg(A) ⊑ tqaff$
- $A$ is _idempotent_, written $urel(sidm, A)$, if $useobg(A) ⊑ tqidm$
- $A$ is _cartesian_, written $urel(scart, A)$, if it is both affine and idempotent
  -- i.e. $useobg(A) ⊑ tqint$

#todo[next sentences were part of the old narrative; fuse better...]

An _affine_ type is precisely a type which can be freely discarded.
A type which is not affine is called _relevant_;
values of such types must be used at least once when introduced.

#todo[Same as the old cartesian system in @cart-ty-wk except for affinity tracking]

We give the rules for subtyping in @ty-wk;
these state that we're allowed to:

- Permute the fields of a product or the variants of a coproduct.

- Coerce the empty type $tzero = Π (·)$ to any type $A$
  (using @twk-zero)

- Drop any _affine_ type $A$ to the unit type $tunit = Π (·)$
  (using @twk-unit)

Combined with congruence, this allows us to repeatedly:

- _Add_ variants to a coproduct:
  "either $A$ or $B$" is a subtype of "either $A$, $B$, or $C$"

- _Remove_ fields from a product:
  _if_ $B$ is _affine_, "both $A$ and $B$" is a subtype of "just $A$"


#fig-r-twk <ty-wk>

#todo[Extending the old notion of a _cartesian_ typing discipline]

More formally, we define a _(substructural) typing discipline_ as follows, 
where _weakening_, in the case of types,
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
  and _cartesian_ if all types are cartesian. #todo-inline[recovering the old definition...]
]

#def-ty-disc

#lemma[
  If $ms("X")$ is a typing discipline, then so is $sty(ms("X"))$.

  Moreover, $sty(ms("X"))$ is affine/idempotent/cartesian iff $ms("X")$ is.
]

#todo[Segue this better, add pointer to figure; also based on older version]

Given a type system $ms("X")$, we define
- A _context_ $Γ ∈ sctx(ms("X"))$ to be a list of variable-type pairs $x : A$ where
  $A ∈ ms("X")$.

  As in the cartesian case, _weakening_ $Γ sle() Δ$, allows us to:
  - Permute the variables in $Γ$
  - Drop variables $x : A$ _where $A$ is affine_
  - Weaken variable types pointwise

  We define the _usage_ obligation of a context $Γ$
  as the meet of the usage obligations of its constituent types.

  In general, we transparently identify contexts $Γ ∈ sctx(ms("X"))$
  and field lists $lb("T") ∈ sstruct(sty(ms("X")))$.

- A _cocontext_ $ms("L") ∈ slctx(ms("X"))$ to be a list of label-type pairs $lb("l")(A)$
  where $A ∈ ms("X")$.

  The rules for weakening cocontexts remain unchanged.

  We define the _usage_ obligation of a cocontext $ms("L")$
  as the meet of the usage obligations of its constituent types.

  In general, we transparently identify cocontexts $ms("L") ∈ slctx(ms("X"))$
  and label lists $lb("L") ∈ sstruct(sty(ms("X")))$.

- A _polycontext_ $cal("L") ∈ sdnf(ms("X"))$ to be a list of tuples $clty(lb("l"), Γ, A)$
  where $Γ ∈ sctx(ms("X"))$ and $A ∈ ms("X")$.

  The rules for weakening polycontexts remain unchanged.

  We define the _usage_ obligation of a cocontext $ms("L")$
  as the meet of the usage obligations of its constituent (context, type) pairs.

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
                                     &&                      useobg(Γ, x : A) & := useobg(Γ) ⊓ useobg(A) \
          useobg(·^⊕) & := tqint &   &&      useobg(ms("L"), lty(lb("l"), A)) & := useobg(ms("L")) ⊓ useobg(A) \
      useobg(·^(⊕ ⊗)) & := tqint &   && useobg(cal("L"), clty(lb("l"), Γ, A)) & := useobg(cal("L")) ⊓ useobg(Γ) ⊓ useobg(A) \
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
  $sctx(ms("X"))$, $slctx(ms("X"))$, and $sdnf(ms("X"))$.

  Moreover,
  $sctx(ms("X"))$, $slctx(ms("X"))$, and $sdnf(ms("X"))$ are affine/idempotent/cartesian
  iff $ms("X")$ is.
]

== Expressions

#todo[Here we go again ; except, we can front-load the effect system]

== Regions

#todo[Here we go yet again; except, again, we can front-load the effect system]

=  Refinement

#todo[this...]

#context if (thesis-state.get)().is-standalone [
  #the-bibliography

  #fig-r-cart-twk <cart-ty-wk>
]
