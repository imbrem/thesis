#import "../../syntax.typ": *
#import "../../todos.typ": *

#show: show-syntax

#context if (thesis-state.get)().is-standalone {
  set document(title: "Type-Theoretic SSA")
  title()
}

The goal of this chapter is to give a formal type-theoretic account of SSA. In particular,
- We begin by giving a type-and-effect system for #iter-calc(), #ssa-calc(), and #gssa-calc()
  from the introduction.
- We use this to build up a _refinement theory_ for #iter-calc(), #ssa-calc(), and #gssa-calc(),
  allowing us to reason about program equivalence and optimization.
- Finally, we formally state and prove the equivalence between the three languages.


= Type System

We want to give a type system for SSA programs, represented as _regions_ $r$.
Our primary judgements will be
$
  haslb(Γ, r, ms("L"))
$
meaning that $r$ is a well-typed SSA program such that:
- given the variables in the _context_ $Γ = x : A, y : B, z : C$ are live on entry,
- when control leaves $r$, it does so by jumping to some label in the _cocontext_
  $ms("L") = lb("l")(A), lb("k")(B), lb("j")(C)$ with a parameter of the appropriate type.

Likewise, we'll need to type _expressions_ $e$, which we'll do in the standard manner using a
judgement of the form $hasty(Γ, e, A)$ -- meaning, "$e$ has type $A$ in context $Γ$".

We'll hence need to define:
- Valid types $A$
- Contexts $Γ$ and cocontexts $ms("L")$

To effectively study _control-flow graphs_, which may have multiple entrypoints,
we will also introduce the notion of a _polycontext_ $cal("L")$, composed of _ports_
$clty(lb("l"), Γ, A)$
associating each entry label $lb("l")$
with a set of live variables $Γ$
and a parameter type $A$.

Along the way, we'll introduce notions of:
- _Subtyping_ $tywk(A, B)$
- _Weakening_ $cwk(Γ, Δ)$ for contexts and $lbcwk(ms("L"), ms("K"))$ for cocontexts
- _Substitutions_ $issubst(Γ, σ, Δ)$ for contexts and
  _label substitutions_ $lbsubst(cal("L"), κ, ms("K"))$ for cocontexts.

  Note that label-substitutions in general take a _polycontext_ as input

and prove some basic syntactic metatheorems.

== Types and Contexts

#import "../rules/types.typ": *

Both our expression calculus #iter-calc() and our SSA region calculus #gssa-calc() use a
system of _simple types_ $A ∈ sty(ms("X"))$ parametrized by a set of _base types_ $X ∈ ms("X")$,
consisting of:

- Atomic types $tybase(X)$ drawn from $ms("X")$ ;
  where it does not introduce ambiguity,
  we make the coercion $tybase((-)) : ms("X") -> sty(ms("X"))$ implicit.

- $n$-ary coproducts /*(_$Σ$-types_)*/ $Σ#lb("L")$ with named variants $lty(lb("l"), A)$ and

- $n$-ary products /*(_$Π$-types_)*/ $Π#lb("T")$ with named fields $lty(lb("f"), A)$,

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
          Or[$Σ#lb("L")$][_Σ (coproduct)_]
          Or[$Π#lb("T")$][_Π (product)_]
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
  In particular, this means that $Π#lb("T")$ and $Π (ρ · lb("T"))$ are _interchangeable_, since
  $
    Π#lb("T") sle() Π (ρ · lb("T")) sle() Π (ρ^(-1) · ρ · lb("T")) = Π#lb("T")
  $
  and likewise for coproducts $Σ#lb("L")$.
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

We can now give grammars and weakening rules for contexts, cocontexts, and polycontexts
in @cart-ctx-grammar-wk. In particular, we define:

- _Contexts_ $Γ ∈ sctx(ms("X"))$ to be a list of variable-type pairs $x : A$ where
  $A ∈ ms("X")$, where no variable $x$ is repeated.

  A context $Γ$ can be viewed as the set of variables live on entry to a program fragment.

  We may _weaken_ a context by _dropping_ unused variables,
  as well as weakening variable types pointwise.
  As $Γ$ is conceptually a _set_, we treat permutations as equivalent under weakening.

  In general, we transparently identify contexts $Γ ∈ sctx(ms("X"))$
  and field lists $lb("T") ∈ sstruct(sty(ms("X")))$.

- _Cocontexts_ $ms("L") ∈ slctx(ms("X"))$ to be a list of label-type pairs $lb("l")(A)$
  where $A ∈ ms("X")$, where no label $ms("l")$ is repeated.

  A cocontext $ms("L")$ records how control may leave a region:
  it is a finite set of exit labels, each annotated with the type of the value passed to that exit.

  We may _weaken_ a cocontext by _adding_ unreachable labels,
  as well as weakening label types pointwise.
  As $ms("L")$ is conceptually a _set_, we treat permutations as equivalent under weakening.

  As usual,
  we represent exits with multiple parameters by providing a single parameter of product type;
  likewise, exits with no parameters simply accept the empty product $tunit$.

  In general, we transparently identify cocontexts $ms("L") ∈ slctx(ms("X"))$
  and label lists $lb("L") ∈ sstruct(sty(ms("X")))$.

- A _polycontext_ $cal("L") ∈ sdnf(ms("X"))$ to be a list of _ports_ of the form
  $clty(lb("l"), Γ, A)$ where $Γ ∈ sctx(ms("X"))$ and $A ∈ ms("X")$,
  where no label $ms("l")$ is repeated.

  When a program fragment has _multiple_ entry points, // (or, dually, exit points),
  we can type it with a _polycontext_ associating each port $lb("l")$ with
  a context of live variables $Γ$ and a parameter type $A$.

  In particular, we may weaken a polycontext by _adding_ unreachable ports,
  as well as weakening port contexts and types pointwise.
  Like for contexts and cocontexts, we treat permutations as equivalent under weakening.

  This construction is used to type case branches, which are entered according
  to a label in $ms("L")$ but share a common incoming context $Γ$;
  to support this common case,
  we define the _lifting_ $Γ csplat ms("L") ∈ sdnf(ms("X"))$
  of a context $Γ$ along a cocontext $ms("L")$ by induction as follows:
  #eqn-set(
    $Γ csplat · := ·$,
    $Γ csplat (ms("L"), lb("l")(A)) := (Γ csplat ms("L")), clty(lb("l"), Γ, A)$,
  )

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
          Or[$Γ, x : A$][$x ∉ Γ$]
        }),
      ),
      bnf(
        Prod($ms("L")$, {
          Or[$·^⊕$][]
          Or[$ms("L"), lty(lb("l"), A)$][$lb("l") ∉ ms("L")$]
        }),
      ),
      bnf(
        Prod($cal("L")$, {
          Or[$·^(⊕ ⊗)$][]
          Or[$cal("L"), clty(lb("l"), Γ, A)$][$lb("l") ∉ ms("L")$]
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
) <cart-ctx-grammar-wk>

Just like for types $sty(ms("X"))$, a typing discipline on $ms("X")$ lists to a typing discipline
on contexts $sctx(ms("X"))$, cocontexts $slctx(ms("X"))$, and polycontexts $sdnf(ms("X"))$:

#lemma[
  If $ms("X")$ is a cartesian typing discipline, then so are
  $sctx(ms("X"))$, $slctx(ms("X"))$, and $sdnf(ms("X"))$
]

== Expressions

#import "../rules/hasty.typ": *

We've now got everything we need to give typing rules for our expression language, #iter-calc().
In particular, we give a grammar for #iter-calc(ms("I")) in @cart-iter-calc-grammar,
parametrized by an _instruction set_ $ms("I") = (ms("F"), ms("A"))$ specifying:

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
    Grammar for #iter-calc(ms("I"))
    for an instruction set $ms("I")$
    with functions $ms("F")$
    and atomic expressions $ms("A")$.
  ],
  kind: image,
)

#iter-calc-grammar <cart-iter-calc-grammar>

In @cart-iter-calc-rules, we give typing rules for the judgements

#judgement-meaning(
  $hasty(Γ, e, A)$,
  ["Expression $e ∈ #iter-calc(ms("F"), ms("A"))$ has type $A$ in $Γ$"],
  $istup(Γ, E, lb("T"))$,
  ["The fields $(E)$ have product type $Π lb("T")$ in $Γ$"],
  $kebrs(cal(K), M, A)$,
  ["The case branches $M$ map inputs $cal(K)$ to output $A$"],
)

parametrized by typing relations:

#judgement-meaning(
  $isfn(Γ, f, A, B)$,
  ["$f ∈ ms("F")$ takes inputs $A$ to outputs $B$ in $Γ$"],
  $hasty(Γ, α, A, annot: ms("A"))$,
  ["Atomic expression $α ∈ ms("A")$ has type $A$ in $Γ$"],
)

#let r-var = rule(
  name: "var",
  $Γ ⊑ x : A$,
  $hasty(Γ, x, A)$,
);
#let r-coe = rule(
  name: "coe",
  $hasty(Γ, a, A)$,
  $tywk(A, A')$,
  $hasty(Γ, a, A')$,
);
#let r-atom = rule(
  name: "atom",
  $hasty(Γ, α, A, annot: ms("A"))$,
  $hasty(Γ, α, A)$,
);
#let r-app = rule(
  name: "app",
  $isfn(Γ, f, A, B, annot: ms("F"))$,
  $hasty(Γ, a, A)$,
  $hasty(Γ, f med a, B)$,
);
#let r-inj = rule(
  name: "inj",
  $hasty(Γ, a, A)$,
  $hasty(Γ, lb("l") med a, Σ (lty(lb("l"), A)))$,
);
#let r-tuple = rule(
  name: "tuple",
  $istup(Γ, E, lb("T"))$,
  $hasty(Γ, (E), Π lb("T"))$,
);
#let r-pi-nil = rule(
  name: "Π-nil",
  $istup(Γ, ·, ·)$,
);
#let r-pi-cons = rule(
  name: "Π-cons",
  $istup(Γ, E, lb("T"))$,
  $hasty(Γ, e, A)$,
  $istup(Γ, #$E, e$, #$lb("T"), fty(lb("f"), A)$)$,
);
#let r-let = rule(
  name: "let",
  $hasty(Γ, a, A)$,
  $hasty(#$Γ, x : A$, b, B)$,
  $hasty(Γ, elet(x, a, b), B)$,
);
#let r-destruct = rule(
  name: [$"let"_n$],
  $hasty(Γ, e_1, Π lb("T"))$,
  $hasty(#$Γ, lb("T")^mb("x")$, e_2, A)$,
  $hasty(Γ, elet((mb("x")), e_1, e_2), A)$,
);
#let r-cases = rule(
  name: "cases",
  $hasty(Γ, e, Σ lb("L"))$,
  $isebrs(Γ, lb("L"), M, A)$,
  $hasty(Γ, ecase(e, M), A)$,
);
#let r-sigma-nil = rule(
  name: "Σ-nil",
  $kebrs(·, ·, A)$,
);
#let r-sigma-cons = rule(
  name: "Σ-cons",
  $kebrs(cal(K), M, A)$,
  $hasty(#$Γ, x : B$, a, A)$,
  $kebrs(#$cal(K), clty(lb("l"), Γ, B)$, #$M, ebr(lb("l"), x, a)$, A)$,
);
#let r-iter = rule(
  name: "iter",
  $hasty(Γ, a, A)$,
  $hasty(Γ, e, B + A)$,
  $hasty(Γ, eiter(a, x, e), B)$,
);

#let fig-r-hasty = figure(
  [
    \
    #rule-set(
      declare-rule(r-var),
      declare-rule(r-atom),
      declare-rule(r-coe),
      declare-rule(r-app),
      declare-rule(r-inj),
      declare-rule(r-tuple),
      declare-rule(r-pi-nil),
      declare-rule(r-pi-cons),
      declare-rule(r-let),
      declare-rule(r-destruct),
      declare-rule(r-cases),
      declare-rule(r-sigma-nil),
      declare-rule(r-sigma-cons),
      declare-rule(r-iter),
    )
    \
  ],
  caption: [
    Typing rules for #iter-calc(ms("I"))
    for an instruction set
    $ms("I")$
    with functions $ms("F")$
    and atomic expressions $ms("A")$
  ],
)

#fig-r-hasty <cart-iter-calc-rules>

More formally, we define:

#definition(name: "Expression Signature")[
  An _expression signature_ $ms("E")$ over a typing discipline $ms("X")$ consists of:
  - A set of _expressions_ $e ∈ E$
  - A typing relation $hasty(Γ, e, A, annot: ms("E"))$
    where $Γ ∈ sctx(ms("X"))$ and $A ∈ ms("X")$
]

Given a cartesian typing discipline $ms("X")$, 
we introduce the cartesian typing discipline of _arrows_
$adisc(ms("X"))$ with
- Types $A → B$ for $A, B ∈ ms("X"))$
- Weakening $(A -> B) ⊑ (A' -> B') := (A' ⊑ A) ∧ (B ⊑ B')$

#definition(name: "Closure Signature")[
  A _closure signature_ $ms("F")$ over a cartesian typing discipline $ms("X")$ is
  defined to be an expression signature over $adisc(ms("X"))$.

  We call elements $f ∈ ms("F")$ _closures_ or _functions_.
]

#definition(name: "Instruction Signature")[
  An _instruction signature_ $ms("I")$ over a typing discipline $ms("X")$ consists of:
  - A closure signature $ms("F")$ over $ms("X")$; for typing _functions_
  - An expression signature $ms("A")$ over $ms("X")$; for typing _atomic expressions_

  We say an instruction signature is _stable under weakening_, or just _stable_, if both
  its closure signature and expression signature are stable.
]

#lemma[
  If $ms("I")$ is an instruction signature over $sty(ms("X"))$,
  where $ms("X")$ is a cartesian typing discipline,
  then #iter-calc(ms("I")) is an expression signature over $sty(ms("X"))$
  with rules for $hasty(Γ, e, A, annot: #iter-calc(ms("I")))$
  given in @cart-iter-calc-rules.
]

In general, we write
- $hasty(Γ, e, A, annot: ms("E"))$ to indicate that $e ∈ ms("E")$ has type $A$ in context $Γ$
- $isfn(Γ, f, A, B, annot: ms("F"))$
  to indicate that $f ∈ ms("F")$ is a function from $A$ to $B$ in
  context $Γ$

Where the signature is unambiguous, we drop the subscript.

A good type system should be well-behaved with respect to:
- _Weakening_: if $cwk(Γ, Δ)$, then anything typing under $Δ$ should also type under $Γ$
- _Subtyping_: if $tywk(A, B)$, then anything typechecking as $A$ should also typecheck as $B$

In particular,

- We say a closure signature is _stable under weakening_, or just _stable_, if, given
  $cwk(Γ, Δ)$ and $tywk(A', A)$, and $tywk(B, B')$, we have
  $
    isfn(Δ, f, A, B, annot: ms("F")) ==> isfn(Γ, f, A', B', annot: ms("F"))
  $

- We say an expression signature is _stable under weakening_, or just _stable_, if, given
  $cwk(Γ, Δ)$ and $tywk(A, A')$, we have
  $
    hasty(Δ, e, A, annot: ms("E")) ==> hasty(Γ, e, A', annot: ms("E"))
  $

- We say an instruction signature is _stable under weakening_, or just _stable_, if both
  its closure signature and expression signature are stable.

As a basic sanity check, we may confirm the following by induction on typing derivations:

#lemma(name: "Weakening")[
  If $ms("I")$ is an instruction signature over a cartesian typing discipline $sty(ms("X"))$ 
  is stable under weakening, then so is #iter-calc(ms("I")).
]

More generally, a good type system should not depend on the names of variables used
-- i.e., it should be _stable under renaming_.

In particular, given a _renaming_ $ρ : renames$ 
-- i.e., a finitely supported injection from variables to variables, where
$
  fsup(ρ) := { x ∈ vset | ρ(x) ≠ x }
$
These form a monoid under composition, with the identity $id$ as unit.

#todo[Make sure renamings are the right way around]

The monoid of renamings acts on contexts $Γ ∈ sctx(ms("X"))$ by pointwise application:
#eqn-set(
  $ρ · (·^⊗) := (·^⊗)$,
  $ρ · (Γ, x : A) := (ρ · Γ), (ρ(x) : A)$,
)
Writing $issubst(Γ, ρ, Δ) := cwk(ρ · Γ, Δ)$, we say that:

- We say a closure signature $ms("F")$
  is _stable under renaming_ if:
  - It is equipped with a monoid action $ρ · f$ of renamings $ρ$ on closures $f ∈ ms("F")$ 
    such that
  - Given a renaming $issubst(Γ, ρ, Δ)$, 
    $isfn(Δ, f, A, B, annot: ms("F"))$ implies
    $isfn(Γ, ρ · f, A, B, annot: ms("F"))$
- Likewise, we say an expression signature $ms("E")$
  is _stable under renaming_ if:
  - It is equipped with a monoid action $ρ · e$ of renamings $ρ$ on expressions $e ∈ ms("E")$ 
    such that
  - Given a renaming $issubst(Γ, ρ, Δ)$, 
    $hasty(Δ, e, A, annot: ms("E"))$ implies
    $hasty(Γ, ρ · e, A, annot: ms("E"))$
- Given an instruction signature $ms("I")$
  - We define a _monoid action_ of renamings on $ms("I")$ to consist of
    an monoid action on its closure signature and a monoid action on its expression signature
  - We say an instruction signature
    is _stable under renaming_ if both
    its closure signature and expression signature are stable under renaming.

Given a monoid action of renamings on an instruction signature $ms("I")$, 
we may define a monoid action of renamings on #iter-calc(ms("I")) by structural recursion,
with action on variables given by $ρ · x := ρ(x)$.

Note in particular that, by $α$-equivalence, we may avoid variable capture by
renaming bound variables to fresh names not appearing in the support of $ρ$.

#lemma(name: "Renaming")[
  If $ms("I")$ is an instruction signature over a cartesian typing discipline $sty(ms("X"))$ 
  that is stable under renaming, then so is #iter-calc(ms("I")).
]

In general, we will assume closure signatures, expression signatures, 
and hence instruction signatures are stable under renaming (and therefore, weakening) by default.
We will call signatures which are _not_ stable under renaming _raw_ signatures.

While we allow atomic expressions and closures to capture variables in general, we can use renamings
to single out the special case where they are in fact constant:

#definition(name: "Function Signature, Constant Signature")[
  A closure signature $ms("F")$ over a cartesian typing discipline $ms("X")$
  is _constant_ if:
  - For all renamings $ρ$, $∀ f ∈ ms("F") . ρ · f = f$
  - For all contexts $Γ$, $hasty(Γ, f, A) <==> hasty(·, f, A)$

  We call a constant closure signature a _function signature_.

  Likewise, an expression signature $ms("A")$ over a cartesian typing discipline $ms("X")$
  is _constant_ if:
  - For all renamings $ρ$, $∀ α ∈ ms("A") . ρ · α = α$
  - For all contexts $Γ$, $hasty(Γ, α, A) <==> hasty(·, α, A)$
]

We would now like to generalize renaming to _substitution_, 
in which we replace variables $x$ with _arbitrary_ expressions $e$.

In particular, we'd like to recover the "usual" notion of substitution:

- A _substitution_ is a finitely supported function $σ : vset → #iter-calc(ms("I"))$, 
  where we define the _support_ of a substitution to be given by
  $
    fsup(σ) := { x ∈ vset | σ(x) ≠ x }
  $

  We write the set of such substitutions as $substs(#iter-calc(ms("I")))$.

- We _apply_ a substitution $σ ∈ substs(#iter-calc(ms("I")))$ 
  to an expression $e ∈ #iter-calc(ms("I"))$;
  written $[σ]e$;
  by recursively replacing each variable $x$ in $e$ with $σ(x)$ 
  -- in particular, as for renamings,
  $α$-renaming allows us to choose fresh variable names for all bound variables 
  to avoid variable capture.

- If $issubst(Γ, σ, Δ)$, defined as, for all $cwk(Δ, x : A)$, $hasty(Γ, σ(x), A)$,
  then $hasty(Δ, e, A)$ implies $hasty(Γ, [σ]e, A)$.

  In this case, we say that the expression signature #iter-calc(ms("I"))
  is _stable under substitution_.

One minor complication of this approach is that we need to define
what it means to substitute functions $f ∈ ms("F")$ and atomic expressions $α ∈ ms("A")$
-- that is, 
to specify an _action_ of the set of substitutions $substs(#iter-calc(ms("I")))$
on $ms("F")$ and $ms("A")$.

It turns out we can fit this into a general framework, along with renaming, as follows:

#definition(name: "Substitution Signature")[
  A _substitution signature_ $ms("S")$ 
  over a cartesian typing discipline $ms("X")$ consists of:
  - A set of _substitutions_ $σ ∈ ms("S")$
  - A typing relation $issubst(Γ, σ, Δ)$
    where $Γ, Δ ∈ sctx(ms("X"))$
  - A partial function from renamings $ρ$ to substitutions $ren2subst(ρ)$
    such that, if $issubst(Γ, ρ, Δ)$ and $ren2subst(ρ)$ is defined,
    then $issubst(Γ, ren2subst(ρ), Δ)$
    --
    when unambiguous, we drop the explicit coercion and simply write $ρ$ for $ren2subst(ρ)$.
  
  We define an _action_ of a substitution signature $ms("S")$ on a set $L$
  to be a mapping from substitutions $σ ∈ ms("S")$ and terms $t ∈ L$
  to their _substitutions_ $σ · t ∈ L$.

  In general, we assume that $ms("S")$ is stable under:
  - _Weakening_: if $cwk(Γ', Γ)$ and $cwk(Δ, Δ')$, then 
    $issubst(Γ, σ, Δ)$ implies $issubst(Γ', σ, Δ')$
  - _Renaming_: 
    $ms("S")$ is equipped with a monoid action 
    of renamings $ρ$ on substitutions $σ ∈ ms("S")$, 
    such that,
    for all renamings $issubst(Γ', ρ, Γ)$, 
    $issubst(Γ, σ, Δ)$ implies $issubst(Γ', ρ · σ, Δ)$

    Moreover, we assume that,
    if $ren2subst(ρ)$ is defined, then 
    - $ρ' · ren2subst(ρ) = ren2subst(ρ' · ρ)$ is defined. 
    - $issubst(Γ, ren2subst(ρ), Δ)$ whenever $issubst(Γ, ρ, Δ)$ 

  If _not_, we say that $ms("S")$ is a _raw substitution signature_.

  We say that:
  - A closure signature $ms("F")$ is _stable under $ms("S")$_ if
    - It is equipped with an action of $ms("S")$ on functions $f ∈ ms("F")$
    - Given a substitution $issubst(Γ, σ, Δ)$,
      $isfn(Δ, f, A, B, annot: ms("F"))$ implies
      $isfn(Γ, σ · f, A, B, annot: ms("F"))$
    - Whenever $ren2subst(ρ)$ is defined, we have $ren2subst(ρ) · f = ρ · f$
    - If $ms("F")$ is in fact constant, then the action of $ms("S")$ is trivial:
      $σ · f = f$ for all $σ ∈ ms("S")$ and $f ∈ ms("F")$
  - An expression signature $ms("E")$ is _stable under $ms("S")$_ if
    - It is equipped with an action of $ms("S")$ on expressions $e ∈ ms("E")$
    - Given a substitution $issubst(Γ, σ, Δ)$,
      $hasty(Δ, e, A, annot: ms("E"))$ implies
      $hasty(Γ, σ · e, A, annot: ms("E"))$
    - Whenever $ren2subst(ρ)$ is defined, we have $ren2subst(ρ) · e = ρ · e$
    - If $ms("E")$ is in fact constant, then the action of $ms("S")$ is trivial:
      $σ · e = e$ for all $σ ∈ ms("S")$ and $e ∈ ms("E")$
  - An instruction signature $ms("I")$ is _stable under $ms("S")$_ if both
    its closure signature and expression signature are stable under $ms("S")$.
]

Immediately, renaming emerges as a base case: $renames$ is a substitution signature over 
_every_ cartesian typing discipline $ms("X")$, with coercion $ren2subst(ρ) := ρ$
simply the identity.

#todo[
  Now, given expression signature $ms("E")$, 
  we define $substs(ms("E"))$ via rules in @cart-subst-rules
]

#let r-subst-nil = rule(
  name: "subst-nil",
  $issubst(Γ, σ, (·^⊗), annot: substs(ms("E")))$,
);

#let r-subst-cons = rule(
  name: "subst-cons",
  $issubst(Γ, σ, Δ, annot: substs(ms("E")))$,
  $hasty(Γ, σ(x), A, annot: ms("E"))$,
  $issubst(Γ, σ, #$Δ, x : A$, annot: substs(ms("E")))$,
)

#figure(
  [
    \
    #rule-set(
      declare-rule(r-subst-nil),
      declare-rule(r-subst-cons),
    )
    \
  ],
  caption: [
    Rules for typing substitutions $σ ∈ substs(ms("E"))$
    in a cartesian typing discipline $ms("X")$.
  ],
) <cart-subst-rules>

#lemma(name: "Substitution")[
  If $ms("I")$ is stable under $substs(#iter-calc(ms("I")))$, then so is #iter-calc(ms("I"))
]

#todo[
  If a substitution $ms("S")$ acts on itself, it is _compositional_
  - compositionally stable == action compatible with composition
  - compositionally stable on self + has id == _monoidal_
]

#todo[
  - If $ms("S")$ acts on $ms("E")$, then it acts on $substs(ms("E"))$
  - If $ms("S")$ acts compositionally on $ms("E")$, 
    then it acts compositionally on $substs(ms("E"))$
    -- and hence $substs(ms("E"))$ is monoidal
  - The below is a _corollary_ of this -- fix that!
]

#lemma(name: "Substitution")[
  If $ms("I")$ is compositionally stable under $substs(#iter-calc(ms("I")))$, 
  then so is #iter-calc(ms("I"))
  -- in particualr, this implies $substs(#iter-calc(ms("I")))$ is monoidal.
]

== Regions

#import "../rules/haslb.typ": *

#todo[recall: goal is a judgement for SSA]

#todo[introduce notion of _region signature_]

#todo[give grammar for _region language_]

#todo[stability under weakening ; renaming of labels]

#todo[adapt below rules for _region language_]

#fig-haslb-br

#fig-haslb-ssa

#todo[SSA is the region language of branches]

#todo[Substitution on SSA -- good!]

#todo[Label renaming -- good!]

#todo[Label substitution -- bad!]

#todo[Extension to fix this:]

#fig-haslb-gssa

#todo[weakening]

#todo[substitution]

#todo[label-substitution]

= Refinement

/*


#todo[
  Alternative ordering: study _refinement_ first; _then_ start studying effects,
  since we need an effect system for _expressions_ to give a sound + complete refinement system.

  Note we _don't_ need a refinement system for _terms_
]

#todo[We want to build up an equational theory...]

#judgement-meaning(
  $lbeq(Γ, ms("R"), r, r', ms("L"))$,
  ["$r$ and $r'$ are equivalent from $Γ$ to $ms("L")$ under $ms("R")$"],
  $tyeq(Γ, ms("R"), e, e', A)$,
  ["$e, e'$ are equivalent at type $A$ in $Γ$ under $ms("R")$"],
)

#todo[(and a _refinement theory_)]

#judgement-meaning(
  $lbref(Γ, ms("R"), r, r', ms("L"))$,
  ["$r$ is refined by $r'$ from $Γ$ to $ms("L")$ under $ms("R")$"],
  $tyref(Γ, ms("R"), e, e', A)$,
  ["$e$ is refined by $e'$ at type $A$ in $Γ$ under $ms("R")$"],
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
  [""Under $ms("R")$, region $r$ maps $Γ$ to $ms("L")$ with effect $ε$""],
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

*/

== Effects

#todo[
  - Introduce _effect systems_
  - This is where we introduce the _quantity lattice_
]

#todo[
  In particular:
  - Not only is substitution not sound in the usual sense sans effects...
  - _But it's not even a congruence_:
    $
      elet(x, ms("load")(p), y + x) ≈ y + ms("load")(p)
    $
    _but_, substituting $(ms("store")(p, 0) ; 0)$ for $y$
    $
      elet(x, ms("load")(p), (ms("store")(p, 0) ; 0) + x)
      ≈ elet(x, ms("load")(p), ms("store")(p, 0) seq x)
    $
    which is not the same as
    $
      (ms("store")(p, 0) ; 0) + ms("load")(p)
      ≈ ms("store")(p, 0) ; ms("load")(p)
      ≈ ms("store")(p, 0) ; 0
    $
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
  Now, we give rules for _refinement_ $->>$;
  discuss:
  - notion of a refinement theory $ms("R")$ on expressions
  - polarity notation $scripts(->>)^p$ to avoid duplicating rules everywhere
  - $(≈) <==> (->> ∧ <<-) <==> (∀ p . scripts(->>)^p)$
]

#todo[
  We say $ehasty(Γ, ms("R"), ε, e, A)$ if _some_ $tyeq(Γ, ms("R"), e, e', A)$ has
]

#todo[
  We want to do _soundness of substitution_ now:
]

#todo[
  We need to give effects to substitutions
]

#todo[
  We can now state _soundness of substitution_
]

#todo[
  Namely, we get nice _$β$-rules_
]

#todo[
  _But_, we can't simplify our equational theory _that_ much unless our effect system is _simple_.

  Later, with substructural types, we can be a bit cleaner.
]

== Regions

#todo[
  Can just directly give a refinement theory for regions,
  _but_ substitution only works for pure stuff
]

#todo[

]

#context if (thesis-state.get)().is-standalone [
  #import "../rules/intro.typ": *

  #the-bibliography

  #ssa-expr-grammar <intro-iter-calc-grammar>
]
