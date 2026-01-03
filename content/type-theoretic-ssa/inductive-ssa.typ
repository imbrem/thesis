#import "../../syntax.typ": *
#import "../../todos.typ": *

#show: show-syntax

#context if (thesis-state.get)().is-standalone {
  set document(title: "Type-Theoretic SSA")
  title()
}

= Type System

#todo[In this section, we start by explaining...]

#judgement-meaning(
  $haslb(Γ, r, ms("L"))$,
  ["Given live variables $Γ$ on input, region $r$ targets labels $ms("L")$ on exit"],
  $hasty(Γ, e, A)$,
  ["Expression $e$ has type $A$ in context $Γ$."],
)

#todo[
  We'll need some types and contexts first; then we can give rules
]

#todo[
  Then we'll prove some basic metatheory:
  - _Weakening_
  - _Substitution_
]

== Types and Contexts

#import "../rules/types.typ": *

#todo[Work on intro: we start with the types]

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
We give the rules for subtyping in @cart-ty-wk;
these state that we're allowed to:

- Permute the fields of a product or the variants of a coproduct.
  In particular, this means that $Π lb("T")$ and $Π (ρ · lb("T"))$ are _interchangeable_, since
  $
    Π lb("T") sle() Π (ρ · lb("T")) sle() Π (ρ^(-1) · ρ · lb("T")) = Π lb("T")
  $
  and likewise for coproducts $Σ lb("L")$.
  We call such interchangeable types $A ≈ B$ _equivalent_, defining
  $
    A ≈ B := A sle() B ⊓ B sle() A
  $

- Coerce the empty type $tzero = Π (·)$ to any type $A$
  (using @cart-twk-zero)

- Drop any type $A$ to the unit type $tunit = Π (·)$
  (using @cart-twk-unit)

Combined with congruence, this allows us to repeatedly:

- _Add_ variants to a coproduct: "either $A$ or $B$" is a subtype of "either $A$, $B$, or $C$"

- _Remove_ fields from a product: "both $A$ and $B$" is a subtype of "just $A$"

In particular, this is a _cartesian_ typing discipline:
we can freely _copy_ and _discard_ values of any type.
// In later chapters, we'll generalize our type theory to support _substructural_
// typing disciplines.

#fig-r-cart-twk <cart-ty-wk>

More formally, we define a _cartesian typing discipline_ as follows,
where _weakening_, in the case of types, corresponds to subtyping:

#let def-ty-disc = definition(name: "Cartesian Typing Discipline")[
  We define a _cartesian typing discipline_ $ms("X")$ to consist of:
  - A set of _types_ $|ms("X")|$.
    Where doing so is unambiguous, we identify $ms("X")$ with its set of types.

  - A preorder $X sle() Y$ on base types, _weakening_.

    We say two types $X, Y$ are _equivalent_, written $X ≈ Y$, if $X sle() Y$ and $Y sle() X$.
]

#def-ty-disc

#lemma[
  If $ms("X")$ is a cartesian typing discipline, then so is $sty(ms("X"))$
]

#todo[Segue to contexts]

Given a typing discipline $ms("X")$, we define
- A _context_ $Γ ∈ sctx(ms("X"))$ to be a list of variable-type pairs $x : A$ where
  $A ∈ ms("X")$.

  Roughly speaking, a context $Γ$ describes the set of variables live on entry to a program
  fragment; hence, weakening on contexts, $Γ sle() Δ$, allows us to:
  - Permute the variables in $Γ$
  - Drop variables $x : A$
  - Weaken variable types

  In general, we transparently identify contexts $Γ ∈ sctx(ms("X"))$
  and field lists $lb("T") ∈ sstruct(sty(ms("X")))$.

- A _cocontext_ $ms("L") ∈ slctx(ms("X"))$ to be a list of label-type pairs $lb("l")(A)$
  where $A ∈ ms("X")$.

  A cocontext $ms("L")$ describes the set of _targets_ a program fragment may jump to on exit,
  each annotated with its parameter type; hence, weakening on cocontexts, $ms("L") sle() ms("M")$,
  allows us to:
  - Permute the labels in $ms("L")$
  - Add new, unreachable labels $lb("l")(A)$
  - Weaken parameter types pointwise

  In general, we transparently identify cocontexts $ms("L") ∈ slctx(ms("X"))$
  and label lists $lb("L") ∈ sstruct(sty(ms("X")))$.

- A _polycontext_ $cal("L") ∈ sdnf(ms("X"))$ to be a list of tuples $clty(lb("l"), Γ, A)$
  where $Γ ∈ sctx(ms("X"))$ and $A ∈ ms("X")$.

  A polycontext $cal("L")$ describes
  the set of _entry points_ or _exit points_ -- _ports_ -- of a control-flow graph,
  with each port $lb("l")$ associated with a context of live variables $Γ$ and a parameter $A$.

  Weakening on polycontexts, $cal("L") sle() cal("M")$ allows us to:
  - Permute the ports in $cal("L")$
  - Add new, unreachable ports $clty(lb("l"), Γ, A)$
  - Weaken live variable contexts and parameters pointwise

  #todo[
    _Explain_ why we need polycontexts and the distributed product $Γ csplat ms("L")$;
    give a better name for $csplat$ too. 
    Currently, $csplat$ becomes $*$ 
    -- consider whether it works or whether we should change this to $⊗$.

    We use polycontexts:
    - So the judgement for case-branches has a polycontext $cal(K)$ as input rather than
      a context $Γ$ + cocontext $ms("L")$ (then, we use $csplat$ to _get_ this polycontext)
    - _Later_, when we add substructural types, a region will in fact target a _polycontext_
      rather than a cocontext; hint at this...
    - It also makes it easier to give a type system for:
      - Label substitution
      - Later, CFGs themselves
  ]

We give a grammar for contexts, cocontexts, and polycontexts, along with rules for weakening,
in @ctx-grammar-wk.

#let r-ctxwk-nil = rule(
  name: "Π-nil",
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
  ],
  kind: image,
  caption: [
    Grammar and typing rules for contexts, cocontexts, and polycontexts.
    When unambiguous, we drop the superscript from the empty list $·$.
  ],
) <ctx-grammar-wk>

#lemma[
  If $ms("X")$ is a cartesian typing discipline, then so are
  $sctx(ms("X"))$, $slctx(ms("X"))$, and $sdnf(ms("X"))$
]

#let field2ctx(T) = $ms("coe")(#T)$
#let var2lctx(L) = $ms("coe")(#L)$

#let ctx2field(Γ) = $ms("coe")(#Γ)$
#let lctx2var(L) = $ms("coe")(#L)$

Given $Γ ∈ sctx(ms("X"))$ and $ms("L") ∈ slctx(ms("X"))$, we may define their
_distributed product_ $Γ csplat ms("L") ∈ sdnf(ms("X"))$
by induction as follows:
#eqn-set(
  $Γ csplat · := ·$,
  $Γ csplat (ms("L"), lb("l")(A)) := (Γ csplat ms("L")), clty(lb("l"), Γ, A)$,
)

== Expressions

#import "../rules/hasty.typ": *

We've now got everything we need to give typing rules for our expression language, #iter-calc().
In particular, we give a grammar for #iter-calc(ms("F"), ms("A")) in @intro-iter-calc-grammar,
parametrized by:

- _functions_ $f ∈ ms("F")$: often, these are our _primitive instructions_ like `add` and `sub`

- _atomic expressions_ $α ∈ ms("A")$:
  in the original grammar from @intro-iter-calc-grammar
  these correspond to _constants_, like `2` and `"hello"`,
  but can be drawn from an arbitrary language $ms("A")$.

#let iter-calc-grammar = figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (4em, 0em),
      bnf(
        Prod(
          $e$,
          {
            Or[$x$][_variable_]
            Or[$α$][_atomic expression_ ($α ∈ ms("A")$)]
            Or[$f med e$][_application_ ($f ∈ ms("F")$)]
            Or[$lb("l") med e$][_label_]
            Or[$(E)$][_structure_]
            Or[$elet(x, e_1, e_2)$][_let-binding_]
            Or[$elet((V), e_1, e_2)$][_destructure_]
            Or[$ecase(e, M)$][_cases_]
            Or[$eiter(e_1, x, e_2)$][_iteration_]
          },
        ),
      ),
      bnf(
        Prod(
          $E$,
          {
            Or[$·$][_nil_]
            Or[$E, fexpr(lb("f"), e)$][_cons_]
          },
        ),
        Prod(
          $K$,
          {
            Or[$·$][_nil_]
            Or[$M seq ebr(lb("l"), x, a)$][_cons_]
          },
        ),
      ),
    )
  ],
  caption: [
    Grammar for #iter-calc(ms("F"), ms("A"))
  ],
  kind: image,
)

#iter-calc-grammar <iter-calc-grammar>

Given typing judgements:

#judgement-meaning(
  $isfn(Γ, f, A, B)$,
  ["In context $Γ$, $f ∈ ms("F")$ takes an input of type $A$ to an output of type $B$"],
  $hasty(Γ, α, A, annot: ms("A"))$,
  ["In context $Γ$, atomic expression $α ∈ ms("A")$ has type $A$"],
)

we give typing rules for judgements

#judgement-meaning(
  $hasty(Γ, e, A)$,
  ["In context $Γ$, expression $e ∈ #iter-calc(ms("F"), ms("A"))$ has type $A$"],
  $istup(Γ, E, lb("T"))$,
  ["In context $Γ$, structure expression $(E)$ has product type $Π lb("T")$"],
  $kebrs(cal(K), M, A)$,
  ["In polycontext $cal(K)$, case branches $M$ yield type $A$"],
)

in @cart-iter-calc-rules.

#todo[
  Now, we formally introduce:
  - _function systems_ $ms("F")$ over a typing discipline $ms("X")$
  - _expression systems_ $ms("E")$ over a typing discipline $ms("X")$
  - Lemma:
    for a typing discipline $ms("X")$,
    if $ms("F")$ is a function system and $ms("A")$ is an expression system,
    then #iter-calc(ms("F"), ms("A")) is an expression system
]

#fig-r-hasty <cart-iter-calc-rules>

== Regions

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

#todo[
  Alternative ordering: study _refinement_ first; _then_ start studying effects,
  since we need an effect system for _expressions_ to give a sound + complete refinement system.

  Note we _don't_ need a refinement system for _terms_
]

#todo[We want to build up an equational theory...]

#judgement-meaning(
  $lbeq(Γ, ms("R"), r, r', ms("L"))$,
  ["Under $ms("R")$, regions $r, r'$ are equivalent when interpreted as taking $Γ$ to $ms("L")$"],
  $tyeq(Γ, ms("R"), e, e', A)$,
  ["Under $ms("R")$, expressions $e, e'$ are equivalent at type $A$ in context $Γ$"],
)

#todo[(and a _refinement theory_)]

#judgement-meaning(
  $lbref(Γ, ms("R"), r, r', ms("L"))$,
  ["Under $ms("R")$, regions $r$ is refined by $r'$ when interpreted as taking $Γ$ to $ms("L")$"],
  $tyref(Γ, ms("R"), e, e', A)$,
  ["Under $ms("R")$, expression $e$ is refined by $e'$ at type $A$ in context $Γ$"],
)

#todo[
  But some equations are only valid depending on effect:
  - $elet(x, a + b, elet(y, c + d, e)) ≈ elet(y, c + d, elet(x, a + b, e))$, _but_
  - $elet(x, ms("input")(), elet(y, ms("input")(), e))
    ≉ elet(y, ms("input")(), elet(x, ms("input")(), e))$
]

#todo[
  So we need a way to track the _effect_ of regions and expressions
]

#judgement-meaning(
  $ehaslb(Γ, ms("R"), ε, r, ms("L"))$,
  ["Under $ms("R")$, 
    given live variables $Γ$ on input, region $r$ targets labels $ms("L")$ on exit with effect $ε$"],
  $ehasty(Γ, ms("R"), ε, e, A)$,
  ["Expression $e$ has type $A$ and effect $ε$ in context $Γ$."],
)

#todo[
  Actual judgement for regions is $ehaslb(Γ, ms("R"), ε, r, ms("L")^ev1)$, 
  where $ev1$ is a map from labels $lb("l")$ to the effect $ε_lb("l")$ of jumping to that label.
]

#todo[
  In fact, we start with _syntactic_ effects 
  $dehasty(Γ, ε, e, A)$,
  $dehaslb(Γ, ε, r, ms("L")^ev1)$
  which don't depend on the equational theory induced by $ms("R")$;
  then actual effect judgements $ehasty(Γ, ms("R"), ε, e, A)$,
  $ehaslb(Γ, ms("R"), ε, r, ms("L")^ev1)$ means there exists some equivalent $e'$, $r'$
  (according to $ms("R")$)
  with the syntactic effect $ε$
]

#todo[
  How to explain refinement?
  - Stick in intro to SSA section, which currently hardly describes equations
  - Equations, then refinement
  - Just refinement
  - Use effects to motivate refinement: $elet(x, ms("maybe-ub"), ()) ->> ()$ but _not_ vice versa...
  - Or, in introduction, talk about how IRs want refinement to deal with UB and friends, then
    use example above to go with effect-dependent refinements...
]

#todo[
  How to explain/motivate effects?
]

== Expressions

#todo[
  We introduce a judgement $dehasty(Γ, ε, e, A)$: the _syntactic_ effect of $e$ 
  in @cart-iter-eff.

  Parametrized by (we assume $ms("F")$ and $ms("A")$ carry these as data...):
]

#judgement-meaning(
  $ehasty(Γ, ms("A"), ε, α, A)$, 
  ["The atomic expression $α$ has effect $ε$ in context $Γ$ at type $A$ in theory $ms("A")$"],
  $eisfn(Γ, ε, f, A, B)$,
  ["The function $f$ has effect $ε$ in context $Γ$ from type $A$ to type $B$"],
)

#todo[
  The rules are mostly the obvious ones; 
  just make sure when we iterate our effect is _actually_ iterative
]

#fig-r-eff-hasty <cart-iter-eff>

#todo[
  Then, we say $ehasty(Γ, ms("R"), ε, e, A)$ if _some_ $tyeq(Γ, ms("R"), e, e', A)$ has
]

== Regions

#todo[introduce _effect labels_ for SSA]

#todo[rules...]

= Refinement

#todo[in fact, want a _refinement theory_]

#todo[(expression) basis ; refinement system _over_ $ms("E")$ ; order]

#todo[basic metatheory]

#todo[(region) basis ; refinement system _over_ $ms("E") ; ms("T")$ ; order embedding]

#todo[basic metatheory]


#context if (thesis-state.get)().is-standalone [
  #import "../rules/intro.typ": *

  #the-bibliography

  #ssa-expr-grammar <intro-iter-calc-grammar>
]
