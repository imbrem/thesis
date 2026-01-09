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
- _Weakening_ $cwk(Γ, Δ)$ for contexts,
  $lbcwk(ms("L"), ms("K"))$ for cocontexts,
  and $cal("L") ⊑ cal("K")$ for polycontexts
- _Substitutions_ $issubst(Γ, γ, Δ)$ for contexts and
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

- $n$-ary coproducts /*(_$Σ$-types_)*/ $Σ#lb("L")$ with named variants $lty(lb("l"), A)$ 
  -- we assume variant tags are drawn from some fixed, infinite set $tset$

- $n$-ary products /*(_$Π$-types_)*/ $Π#lb("T")$ with named fields $lty(lb("f"), A)$,
  -- we assume field names are drawn from some fixed, infinite set $fset$

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
  $A ∈ ms("X")$, where no variable $x$ is repeated
  -- we assume a fixed, infinite set of variables $vset$ to draw from.

  A context $Γ$ can be viewed as the set of variables live on entry to a program fragment.

  We may _weaken_ a context by _dropping_ unused variables,
  as well as weakening variable types pointwise.
  As $Γ$ is conceptually a _set_, we treat permutations as equivalent under weakening.

  In general, we transparently identify contexts $Γ ∈ sctx(ms("X"))$
  and field lists $lb("T") ∈ sstruct(sty(ms("X")))$,
  transporting variables along a distinguished isomorphism $var2fld : vset ≈ fset$.

- _Cocontexts_ $ms("L") ∈ slctx(ms("X"))$ to be a list of label-type pairs $lb("l")(A)$
  where $A ∈ ms("X")$, where no label $ms("l")$ is repeated
  -- we assume a fixed, infinite set of labels $lset$ to draw from.

  A cocontext $ms("L")$ records how control may leave a region:
  it is a finite set of exit labels, each annotated with the type of the value passed to that exit.

  We may _weaken_ a cocontext by _adding_ unreachable labels,
  as well as weakening label types pointwise.
  As $ms("L")$ is conceptually a _set_, we treat permutations as equivalent under weakening.

  As usual,
  we represent exits with multiple parameters by providing a single parameter of product type;
  likewise, exits with no parameters simply accept the empty product $tunit$.

  In general, we transparently identify cocontexts $ms("L") ∈ slctx(ms("X"))$
  and label lists $lb("L") ∈ sstruct(sty(ms("X")))$, 
  transporting labels along a distinguished isomorphism $lab2tag : lset ≈ tset$.

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

  We will, where it does not introduce ambiguity, transparently identify a cocontext $ms("L")$
  with the polycontext $(·^⊗) csplat ms("L")$
  associating every label with the empty variable context.

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

#todo[Why do we care about renaming]

We define a _renaming_ $ρ : vrens$ to be a finitely supported injection, where the _support_ of a
function $ρ : vset → vset$ is defined as
$
  fsup(ρ) := { x ∈ vset | ρ(x) ≠ x }
$
This in particular forms a monoid, with multiplication $ρ_1 ρ_2 = ρ_1 ∘ ρ_2$
and identity $id : vrens$.

#definition(name: "Renaming")[
  A cartesian typing discipline $ms("X")$ supports _renaming_ 
  if it is equipped with a left monoid action
  of renamings $ρ : vrens$ on types $X ∈ ms("X")$ such that, 
  for all $ρ$, $λ X qd ρ X$ is an order automorphism on $ms("X")$ 
  -- i.e. it preserves and reflects weakening.
]

In particular,
- Renaming for contexts is pointwise: $ρ (Γ, x : A) := (ρ Γ), ρ(x) : A$, and $ρ (·^⊗) := (·^⊗)$
- Renaming for cocontexts is the identity: $ρ (ms("L")) := ms("L")$
- Renaming for polycontexts is pointwise: 
  $ρ (cal("L"), clty(lb("l"), Γ, A)) 
  := (#$ρ$cal("L")), clty(lb("l"), ρ Γ, A)$, and $ρ (·^(⊕ ⊗)) := (·^(⊕ ⊗))$

Dually, we define a _relabeling_ $ρ : lrens$ to be a finitely supported injection on labels,
where the _support_ of a function $ρ : lset → lset$ is defined as
$  
fsup(ρ) := { l ∈ lset | ρ(l) ≠ l } 
$
This in particular forms a monoid, with multiplication $ρ_1 ρ_2 = ρ_1 ∘ ρ_2$
and identity $id : lrens$.

#definition(name: "Relabeling")[
  A cartesian typing discipline $ms("X")$ supports _relabeling_ 
  if it is equipped with a right monoid action
  of relabelings $ρ : lrens$ on types $X ∈ ms("X")$ such that, 
  for all $ρ$, $λ X qd X ρ$ is an order automorphism on $ms("X")$ 
  -- i.e. it preserves and reflects weakening.
]

In particular,
- Relabeling for contexts is the identity: $Γ ρ := Γ$
- Relabeling for cocontexts is pointwise: $(ms("L"), lb("l")(A)) ρ := (ms("L")), (ρ(lb("l")))(A)$
- Relabeling for polycontexts is pointwise:
  $(cal("L"), clty(lb("l"), Γ, A)) ρ := (cal("L")), clty(ρ(lb("l")), Γ, A)$

We note in particular that:
#eqn-set(
  $ρ_vset (Γ csplat ms("L")) = (ρ_vset Γ) csplat ms("L")$,
  $(Γ csplat ms("L")) ρ_lset = Γ csplat (ms("L") ρ_lset)$,
)

== Expressions

#import "../rules/hasty.typ": *

#let dof = ms("O")
#let dfnl = ms("F")
#let dael = ms("A")
#let dic = iter-calc(dof)
#let daic = iter-calc(dael)
#let dfic = iter-calc(dfnl)

We've now got everything we need to give typing rules for our expression language, #iter-calc().

We give a grammar for #dic in @cart-iter-calc-grammar,
parametrized by an _operator family_ $#dof = (dfnl, dael)$ specifying:

- _functions_ $f ∈ dfnl$: 
  in the introduction, these are our _primitive instructions_ like `add` and `sub`,
  but in general these can be drawn from an arbitrary language $dfnl$
  -- in particular, they may be allowed to capture variables, which case we call $f$ a _closure_.

- _atomic expressions_ $α ∈ dael$:
  in the original grammar from @intro-iter-calc-grammar
  these correspond to _constants_ $c$, like `2` and `"hello"`,
  but in general these can be drawn from an arbitrary language $dael$.

We'll call $dof$ an _instruction set_ when $dfnl$ and $dael$ are in 
fact restricted to _closed_ functions and constants respectively.

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
            Or[$α$][_atomic expression_ ($α ∈ dael$)]
            Or[$f med e$][_application_ ($f ∈ dfnl$)]
            Or[$lb("l") med e$][_label_]
            Or[$(E)$][_structure_]
            Or[$elet(x, e_1, e_2)$][_let-binding_]
            Or[$elet((mb("x")), e_1, e_2)$][_destructure_]
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
    Grammar for #dof
    for an instruction set #dic
    with functions $dfnl$
    and atomic expressions $dael$.
  ],
  kind: image,
)

#iter-calc-grammar <cart-iter-calc-grammar>

In @cart-iter-calc-rules below, we proceed to give typing rules for the judgements

#judgement-meaning(
  $hasty(Γ, e, A, annot: dic)$,
  ["Expression $e ∈ dic$ has type $A$ in $Γ$"],
  $istup(Γ, E, lb("T"), annot: dic)$,
  ["The fields $(E)$ have product type $Π lb("T")$ in $Γ$"],
  $kebrs(cal(K), M, A, annot: dic)$,
  ["The case branches $M$ map inputs $cal(K)$ to output $A$"],
)

parametrized by typing relations:

#judgement-meaning(
  $isfn(Γ, f, A, B, annot: dfnl)$,
  ["$f ∈ dfnl$ takes inputs $A$ to outputs $B$ in $Γ$"],
  $hasty(Γ, α, A, annot: dael)$,
  ["Atomic expression $α ∈ dael$ has type $A$ in $Γ$"],
)

Where clear from context, we drop the subscript on the turnstile specifying the type system in use.

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
  $hasty(Γ, α, A, annot: dael)$,
  $hasty(Γ, α, A)$,
);
#let r-app = rule(
  name: "app",
  $isfn(Γ, f, A, B, annot: dfnl)$,
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
  $kebrs(Γ csplat lb("L"), M, A)$,
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
  $kebrs(#$cal(K), clty(lb("l"), Γ, B)$, #$(M, ebr(lb("l"), x, a))$, A)$,
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
      declare-rule(r-var, label: <r-cart-var>),
      declare-rule(r-atom, label: <r-cart-atom>),
      declare-rule(r-app, label: <r-cart-app>),
      declare-rule(r-inj, label: <r-cart-inj>),
      declare-rule(r-tuple, label: <r-cart-tuple>),
      declare-rule(r-pi-nil),
      declare-rule(r-pi-cons),
      declare-rule(r-let, label: <r-cart-let>),
      declare-rule(r-destruct, label: <r-cart-destruct>),
      declare-rule(r-cases, label: <r-cases>),
      declare-rule(r-sigma-nil),
      declare-rule(r-sigma-cons),
      declare-rule(r-iter, label: <r-cart-iter>),
      declare-rule(r-coe, label: <r-cart-coe>),
    )
    \
  ],
  caption: [
    Typing rules for #$hasty(Γ, e, A, annot: dic)$
    for an _instruction set_
    $dof = (dfnl, dael)$
  ],
)

#fig-r-hasty <cart-iter-calc-rules>

More formally, 
#definition(name: [Typing relation, typed syntax])[
  Given cartesian typing disciplines $ms("X")$ and $ms("Y")$,
  we define a _pretyping relation_ $srel(ms("S")) : ms("X") stfn(S) ms("Y")$ over a _syntax_ $S$ 
  to consist of a ternary relation $hasty(X, s, Y, annot: ms("S"))$
  over _inputs_ $X ∈ |ms("X")|$, _terms_ $s ∈ S$, and _outputs_ $Y ∈ |ms("Y")|$.

  - _closed_ if it does not depend on its input -- i.e., for all inputs $X ⊑ X' ∈ |ms("X")|$,
    #space-iff(
      $hasty(X, s, Y, annot: ms("S"))$,
      $hasty(X', s, Y, annot: ms("S"))$,
    )

  We define a _pretyped syntax_ $ms("S")$ to consist of:
  - A set of _terms_ $|ms("S")|$
  - A pretyping relation $srel(ms("S")) : ms("X") stfn(|ms("S")|) ms("Y")$

  Where there is no risk of confusion, we identify $ms("S")$ with its set of terms.

  We say $ms("S")$ is a _stable under (input/output) weakening_ if $srel(ms("S"))$ is
  -- if $ms("S")$ is stable under weakening, we call $ms("S")$ a _typed syntax_.
]

#definition(name: [Operator family])[
  Given cartesian typing disciplines $ms("X")$ and $ms("Y")$,
  a _pre-operator family_ $dof = (dfnl, dael) : hpop(ms("X"), ms("Y"))$ 
  from $ms("X")$ to $ms("Y")$ consists of:
  - A pretyped syntax $opfn(dof) := dfnl : ms("X") → adisc(ms("Y"))$ of _functions_
  - A pretyped syntax $opatom(dof) := dael : ms("X") → ms("Y")$ of _atomic expressions_
  where $adisc(ms("Y"))$ is the cartesian typing discipline of _$ms("Y")$-arrows_ with
  - Types $A -> B$ for $A, B ∈ |ms("Y")|$
  - Weakening $(A -> B) sle() (A' -> B') := tywk(A', A) ⊓ tywk(B, B')$
    -- that is, $->$ is _contravariant_ in its input and _covariant_ in its output.

  Likewise, if $dfnl$ and $dael$ are closed, we say $dof$ is closed.

  We define the _pre-operator families over $ms("X")$_, written $spop(ms("X"))$, to be given by
  $
    spop(ms("X")) := hpop(sctx(ms("X")), ms("X"))
  $
]

We may now define 
#definition(name: [Iteration expressions])[
  Given a pretyped instruction set $ms("I") : spop(sty(ms("X")))$, 
  we define the pretyped syntax of _iteration expressions_ $dic$ to consist of:
  - Terms $|dic|$ given by the grammar in @cart-iter-calc-grammar
  - Typing relation $hasty(Γ, e, A, annot: dic)$ given by the rules in @cart-iter-calc-rules
]

Given a pretyping relation on atomic expressions $hasty(Γ, α, A, annot: dael)$,
we write #daic for #iter-calc($(tzero, dael)$),
where $tzero$ is the _empty_ function syntax
(in which every function _vacuously_ has every type).

In particular, this means that $hasty(Γ, e, A, annot: daic)$
if and only if $hasty(Γ, e, A, annot: #iter-calc($(dfnl, dael)$))$
_for all_ choices of function syntax $dfnl$.

Likewise, given a pretyping relation on functions $isfn(Γ, f, A, B, annot: dfnl)$,
we write #dfic for #iter-calc($(dfnl, tunit)$),
where $tunit$ is the _empty_ atomic expressions syntax
in which every atomic expression _vacuously_ has every type.

In particular, this means that $hasty(Γ, e, A, annot: #dfic)$
if and only if $hasty(Γ, e, A, annot: #iter-calc($(dfnl, dael)$))$
_for all_ choices of atomic expression syntax $dael$.

More generally, we define:
$
  ms("S")_1 ⊆ ms("S")_2 := 
    |ms("S")_1| ⊆ |ms("S")_2| 
    ∧ ∀ s ∈ ms("S")_1 qd hasty(Γ, s, A, annot: ms("S")_1) ==> hasty(Γ, s, A, annot: ms("S")_2)
$
In particular, this is a partial order on pretyped syntax, with bottom element $mb(0) ⊆ ms("S")$,
and joins and meets given by union and intersection respectively as follows:
#eqn-set(
  $⋃_i ms("S")_i := (⋃_i |ms("S")_i|, (λ Γ, s, a qd ⋁_i hasty(Γ, s, A, annot: ms("S")_i)))$,
  $⋂_i ms("S")_i := (⋂_i |ms("S")_i|, (λ Γ, s, a qd ⋀_i hasty(Γ, s, A, annot: ms("S")_i)))$
)

In general, #iter-calc() preserves subsets:
#space-imp(
  $dof ⊆ dof'$,
  $#iter-calc(dof) ⊆ #iter-calc($dof'$)$
)
where we define
$
  (dof ⊆ dof') := 
    (opfn(dof) ⊆ opfn(dof')) ∧ (opatom(dof) ⊆ opatom(dof'))
$

As a quick sanity check, we want to verify that our type system(s) respect _weakening_
by a straightforward induction:
- If $hasty(Δ, e, A, annot: dic)$, 
  then adding unused variables to $Δ$ can't make $e$ ill-typed.
- That is, if $Γ ⊑ Δ$ and $hasty(Δ, e, A, annot: dic)$,
  then $hasty(Γ, e, A, annot: dic)$.

Since our weakening relation $Γ ⊑ Δ$ also includes permutations, this also subsumes _exchange_:
for any permutation $σ$, $hasty(Γ, e, A, annot: dic) <==> hasty(σ · Γ, e, A, annot: dic)$.
For this to be true, however, we need to ensure that the typing relations for 
$ms("F")$ and $ms("A")$ satisfy weakening as well.

Formally,
#definition(name: "Typing Relation")[
  We say $srel(ms("S"))$ is:
  - _stable under input weakening_ if, for all inputs $X' ⊑ X$, 
    $hasty(X, s, Y, annot: ms("S"))$ implies $hasty(X', s, Y, annot: ms("S"))$.

    That is, if $srel(ms("S"))$ is _contravariant_ in its input (w.r.t. the weakening order).

  - _stable under output weakening_ if, for all outputs $Y ⊑ Y'$, 
    $hasty(X, s, Y, annot: ms("S"))$ implies $hasty(X, s, Y', annot: ms("S"))$.

    That is, if $srel(ms("S"))$ is _covariant_ in its output (w.r.t. the weakening order).

  - _stable under weakening_ if it is stable under both input and output weakening
    -- i.e., it is a _profunctor_ w.r.t. the weakening order.

    In this case, we call $srel(ms("S"))$ a _typing relation_.
]

We say $dof$ is _stable under (input/output) weakening_ 
if both $dfnl$ and $dael$ are stable under (input/output) weakening.
-- if $dof$ is stable under weakening, we say $dof$ is a _(typed) operator family_.

We can then state our _weakening lemma_ as follows:

#lemma(name: [Weakening (#dic)])[
  If #dof is stable under input weakening, then #dic is stable under weakening
  -- i.e. for all $Γ ⊑ Δ$ and $tywk(A, B)$,
  #space-imp(
    $hasty(Δ, e, A, annot: dic)$,
    $hasty(Γ, e, B, annot: dic)$,
  )
]

A good type system should also not depend on the particular choice of variable names in our context,
and hence in particular should be invariant under _renaming_
-- 
  replacing every variable $x$ with $ρ x$ for some renaming 
  $ρ : vrens$ should preserve well-typedness.

Concretely, we expect that a term
$hasty(Γ, e, A)$ typechecks if and only if $hasty(ρ Γ, ρ e, A)$ typechecks, whenever
$ρ : vrens$ is a renaming -- for this to hold, we need both that:
- The typing relations for $ms("F")$ and $ms("A")$ support renaming
- We have a well-defined notion of renaming on expressions $ρ e$

It turns out that expressions in fact support a more general operation than renaming
-- namely, _substitution_ -- in which each variable $x : A$ in a context $Δ$ 
is replaced with an arbitrary _term_ $hasty(Γ, e, A)$ 
(which can, but does not have to, be a variable $y$ in $Γ$).

In particular, we define:

- A _substitution_ is a finitely supported function $γ : vset → ms("E")$,
  where we define the _support_ of a function $γ : vset → ms("E")$ to be given by
  $
    fsup(γ) := { x ∈ vset | γ(x) ≠ x }
  $
  for $vset ⊆ ms("E")$. We write the set of such functions as $substs(#ms("E"))$.

- We _apply_ a substitution $γ ∈ substs(#dic)$
  to an expression $e ∈ #dic$;
  written $γ · e$.

  For _expressions_, this is done by structural recursion on $e$,
  replacing each variable $x$ in $e$ with $γ(x)$: we give the full definition in
  @cap-avoid-iter-subst-rules.

  #figure(
    [
      #eqn-set(
        $γ · x := γ(x)$,
        $γ · α := γ ·_dael α$,
        $γ · (f med e) := (γ ·_dfnl f) med (γ · e)$,
        $γ · (lb("l") med e) := lb("l") med (γ · e)$,
      )
      $
        γ · (E) := (γ · E)
        " where "
        γ · (·_E) := ·_E, #h(1em)
        γ · (E, fty(lb("f"), a)) := (γ · E, fty(lb("f"), γ · a))
      $
      $
                γ · (elet(x, e_1, e_2)) & := (elet(x, γ · e_1, γ · e_2)) //
                                            & #h(1em) & "(choosing " x ∉ fsup(γ)")" \
        γ · (elet((mb("x")), e_1, e_2)) & := (elet((mb("x")), γ · e_1, γ · e_2)) //
                                            &         & "(choosing " mb("x") ∩ fsup(γ) = ∅")" \
                 γ · eiter(e_1, x, e_2) & := eiter(γ · e_1, x, γ · e_2) //
                                            &         & "(choosing " x ∉ fsup(γ)")"
      $
      $
        & γ · ecase(e, M) := ecase(γ · e, γ · M) "where" \
        & #h(2em) γ · (·_M) := (·_M), \
        & #h(2em) γ · (M, ebr(lb("l"), x, a)) := (γ · M, ebr(lb("l"), x, γ · a))
          #h(2em) "(choosing " x ∉ fsup(γ)")"
      $
      \
      where we are given
      \
      $
        (·_dael) &: substs(#dic) → dael → #dic
        & #h(3em) & "(substitution on atomic expressions)"
        \
        (·_dfnl) &: substs(#dic) → dfnl → dfnl
        && "(substitution on closures)"
      $
      \
    ],
    caption: [
      Capture-avoiding substitution on expressions $e ∈ #dic$
    ],
  ) <cap-avoid-iter-subst-rules>

  In particular,
  - Our substitution is _capture-avoiding_:
    $α$-renaming allows us to choose fresh names $x ∉ fsup(γ)$ for all bound variables.
  - We need to provide definitions for
    - Substitutions on _closures_ $γ ·_dfnl f$
    - Substitutions on _atomic expressions_ $γ ·_dael α$
    In the case of constant closures (functions) and constant atomic expressions (constants),
    these are simply the identity.

  Substitutions $γ ∈ substs(#dic)$ in fact form a _monoid_, with
  - Unit the identity substitution $id(x) = x$
  - Multiplication given by composition: $(γ_1γ_2)(x) := γ_1 · (γ_2(x))$
  making $γ · e$ into a _monoid action_ of
  $substs(#dic)$ on $#dic$,
  whenever substitution on closures and atomic expressions
  also form monoid actions -- i.e., whenever we have
  #eqn-set(
    $id ·_dael α = α$,
    $(γ_1γ_2) ·_dael α = γ_1 ·_dael (γ_2 ·_dael α)$,
  )
  #eqn-set(
    $id ·_dfnl f = f$,
    $(γ_1γ_2) ·_dfnl f = γ_1 ·_dfnl (γ_2 ·_dfnl f)$,
  )
  (otherwise, multiplication of substitutions is still _well-defined_, but may not form a monoid).

  Where the desired meaning is clear from context, 
  we write application $γ · e$ as juxtaposition $γ e$.

- We say that $γ : substs(ms("E"))$ is a _substitution_ from context $Δ$ to context $Γ$,
  written $issubst(Γ, γ, Δ, annot: substs(ms("E")))$,
  if, for each $x : A$ s.t. $cwk(Δ, x : A)$,
  we have that $hasty(Γ, γ(x), A, annot: ms("E"))$.

  More formally, we give typing rules for $issubst(Γ, γ, Δ)$ in @cart-iter-subst-rules.

  We note that:
  
  - This equips $substs(ms("E"))$ with the structure of a pretyped syntax
    whenever $ms("E")$ is a pretyped syntax 
    -- morever, if $ms("E")$ is stable under (input/output) weakening, then so is $substs(ms("E"))$.

    In particular, this means that if $ms("E")$ is a typed syntax, then so is $substs(ms("E"))$.

  - Every _renaming_ $ρ : vrens$ can be taken as a substitution $issubst(ρ Γ, ρ, Γ)$

  - Every renaming is _injective_, and hence has an _inverse_ substitution
    $issubst(Γ, ρ^(-1), ρ Γ)$
    (where, whenever $ρ^(-1)$ is undefined, we take $ρ^(-1)(y) = y$).

#let r-iter-subst-nil = rule(
  name: "subst-nil",
  $issubst(Γ, γ, (·^⊗), annot: substs(ms("E")))$,
);

#let r-iter-subst-cons = rule(
  name: "subst-cons",
  $issubst(Γ, γ, Δ, annot: substs(ms("E")))$,
  $hasty(Γ, γ(x), A, annot: ms("E"))$,
  $issubst(Γ, γ, #$Δ, x : A$, annot: substs(ms("E")))$,
)

#figure(
  [
    \
    #rule-set(
      declare-rule(r-iter-subst-nil),
      declare-rule(r-iter-subst-cons),
    )
    \
  ],
  caption: [
    Rules for typing substitutions $γ ∈ substs(ms("E"))$
  ],
) <cart-iter-subst-rules>

#definition(name: "Renaming, Operation Family")[
  We say a pretyping relation $ms("E") : ms("X") stfn(S) ms("Y")$ is _stable under renaming_ if
  - $ms("X")$ and $ms("Y")$ support renaming
  - $S$ is equipped with a distinguished monoid action
    $ρ · s ∈ S$ of renamings $ρ : vrens$ on terms $s ∈ S$
  such that, for all renamings $ρ : vrens$,
  #space-iff(
    $hasty(X, s, Y, annot: ms("E"))$,
    $hasty(ρ X, ρ s, ρ Y, annot: ms("E"))$,
  )

  We define an _operation family_ $dof = (dfnl, dael)$ to be a preoperation family 
  such tha $dfnl$ and $dael$ are both stable under renaming and weakening --
  we write
  - The set of operation families from $ms("X")$ to $ms("Y")$ as 
    $hop(ms("X"), ms("Y")) ⊆ hpop(ms("X"), ms("Y"))$
  - The set of operation families over $ms("X")$ as 
    $sop(ms("X")) := hop(sctx(ms("X")), ms("X")) ⊆ spop(ms("X"))$
]

#definition(name: [Substitutive])[
  We say that a pretyped syntax $ms("E") : sctx(ms("X")) sfn ms("X")$ is _substitutive_ if
  - $ms("Var") ⊆ ms("E")$
  - $ms("E")$ is stable under renaming
  - $|ms("E")|$ is equipped with an action
    $γ · e ∈ ms("E")$ of substitutions $γ ∈ substs(ms("E"))$ on terms $e ∈ ms("E")$
  such that:
  - $(γ_1γ_2) · e = γ_1 · (γ_2 · e)$, where $(γ_1γ_2)(x) = γ_1 · (γ_2(x))$
  - For all substitutions $issubst(Γ, γ, Δ)$ and $hasty(Δ, e, A)$,
    we have $hasty(Γ, γ · e, A)$ -- moreover
  - Given $∀ x ∈ Δ qd γ'(x) = γ(x)$, $γ' · e = γ · e$, and, in particular,
  - If, given a renaming $ρ$, $∀ x ∈ Δ qd ρ(x) = γ(x)$,
    then $γ · e = ρ · e$
    where the right-hand side is the renaming action on $ms("E")$
    -- i.e., substitution extends renaming.

    Therefore, in particular, $id · e = e$.

  We call a substitutive typed syntax $ms("E") : sctx(ms("X")) sfn ms("X")$ 
  an _expression syntax (over $ms("X")$)_
  -- we write the set of such syntaxes as $sexpr(ms("X"))$.
]

To show that $dic$ is in fact substitutive 
-- and therefore an expression syntax over $sty(ms("X"))$ --
we need to be able to substitute functions in $dfnl$
and atomic expressions in $dael$ as well -- i.e., we need to show that $dof$ is compatible with
$dic$-substitutions. The definition of substitutive, 
however, doesn't generalize directly to operator families, 
since it doesn't even make sense to consider substitutions $substs(dof)$.
Instead, we proceed as follows:

#definition(name: [$ms("V")$-Substitutive])[ 
  Given an expression syntax $ms("V") : sexpr(ms("X"))$,
  we say that a pretyped syntax $ms("E") : sctx(ms("X")) sfn ms("Y")$ 
  is _$ms("V")$-substitutive_ if
  - $ms("E")$ is stable under renaming
  - $|ms("E")|$ is equipped with an action
    $γ · e ∈ ms("E")$ of substitutions $γ ∈ substs(ms("V"))$ on terms $e ∈ ms("E")$
  such that:
  - $(γ_1γ_2) · e = γ_1 · (γ_2 · e)$, where $(γ_1γ_2)(x) = γ_1 · (γ_2(x))$
  - For all substitutions $issubst(Γ, γ, Δ)$ and $hasty(Δ, e, A)$,
    we have $hasty(Γ, γ · e, A)$ -- moreover
  - Given $∀ x ∈ Δ qd γ'(x) = γ(x)$, $γ' · e = γ · e$, and, in particular,
  - If, given a renaming $ρ$, $∀ x ∈ Δ qd ρ(x) = γ(x)$,
    then $γ · e = ρ · e$
    where the right-hand side is the renaming action on $ms("E")$
    -- i.e., substitution extends renaming.

    Therefore, in particular, $id · e = e$.
]

We say that a pre-operator family $dof = (dfnl, dael)$ is _$ms("V")$-substitutive_ if
both $dfnl$ and $dael$ are both $ms("V")$-substitutive.

In general, we then note that:
- $ms("E")$ is an expression syntax iff it is $ms("E")$-substitutive
- $mb("0")$ is $ms("V")$-substitutive for all substitutive $ms("V")$

In general, we want that, if $ms("E")$ is _closed_, i.e. does not depend on variables,
then $ms("E")$ should be $ms("V")$-substitutive for all substitutive $ms("V")$.

#definition(name: [Closed])[
  We say that a pretyped syntax $ms("E") : ms("X") sfn ms("Y")$ is _closed_ if:
  - For all inputs $X ⊑ X' ∈ |ms("X")|$, 
    $hasty(X, e, Y, annot: ms("E")) <==> hasty(X', e, Y, annot: ms("E"))$
  - $ms("X")$ and $ms("Y")$ support renaming
  - The action of renamings $ρ : vrens$ on terms $e ∈ ms("E")$ is the identity 
    -- $∀ ρ, e qd ρ · e = e$
]

In this case, for any $ms("E") : sctx(ms("X")) sfn ms("Y")$ closed, 
given $ms("V") : sexpr(ms("X"))$,
we may equip $ms("E")$ with the structure of a $ms("V")$-substitutive syntax by
defining $γ · e := e$ for all substitutions $γ ∈ substs(ms("V"))$.

#definition(name: [Instruction Set])[
  We say an operator family $dof = (dfnl, dael)$ is an _instruction set_ if
  $dfnl$ and $dael$ are both closed.

  We write: 
  - the set of instruction sets from $ms("X")$ to $ms("Y")$ as
    $hinst(ms("X"), ms("Y")) ⊆ hop(ms("X"), ms("Y"))$
  - the set of instruction sets over $ms("X")$ as
    $sinst(ms("X")) := hinst(sctx(ms("X")), ms("X")) ⊆ sop(ms("X"))$
]

In particular, it follows that every instruction set over $ms("X")$ is $ms("V")$-substitutive for
all substitutive $ms("V") : sexpr(ms("X"))$.

We can now give our _substitution lemma_ for $#dic$ as follows:

#lemma(name: "Substitution")[
  If $dof$ is $dic$-substitutive,
  then so is #dic --
  i.e. for all $issubst(Γ, γ, Δ)$ and $hasty(Δ, e, A)$,
  $
    hasty(Γ, γ · e, A)
  $
]

#todo[Segue to values]

We define a grammar for _values_
$#val-calc(dael)$ (parametrized by atomic expressions $α ∈ dael$)
and single operations
$#inst-calc(dof)$
(parametrized by an _operator family_ $dof = (dfnl, dael)$)
below:

#let val-calc-grammar = figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (4em, 0em),
      bnf(
        Prod(
          $o ∈ #inst-calc(dof)$,
          {
            Or[$v$][_value_]
            Or[$f med v$][_instruction_]
            Or[$lb("l") med v$][_label_]
          },
        ),
        Prod(
          $v ∈ #val-calc(dael)$,
          {
            Or[$x$][_variable_]
            Or[$α$][_atomic expression_ ($α ∈ dael$)]
            Or[$(V)$][_tuple_]
          },
        ),
      ),
      bnf(
        Prod(
          $V$,
          {
            Or[$·$][_nil_]
            Or[$V, fexpr(lb("f"), v)$][_cons_]
          },
        ),
      ),
    )
    \
    $
      #val-calc(dael) #h(2em) ⊆ #h(2em) #inst-calc(dof) #h(2em) ⊆ #h(2em) #dic
      #h(3em) "for" #h(3em)
      dof = (dfnl, dael)
    $
    \
  ],
  caption: [
    Grammar for #dic
    for an instruction set $dof$
    with functions $dfnl$
    and atomic expressions $dael$.
  ],
  kind: image,
)

#val-calc-grammar <val-calc-grammar>

We type values and operations as a subset of expressions in #dic -- that is, 
$
  #val-calc(dael) #h(2em) ⊆ #h(2em) #inst-calc(dael) #h(2em) ⊆ #h(2em) #iter-calc(dael)
$
and
$
  #inst-calc(dof) #h(2em) ⊆ #h(2em) #iter-calc(dof)
$
and hence
$
  ∀ v ∈ #val-calc(dael) qd &
    hasty(Γ, v, A, annot: #val-calc(dael)) 
    &&<==> hasty(Γ, v, A, annot: #inst-calc(dael))
    &&<==> hasty(Γ, v, A, annot: #iter-calc(dael))
    \
  ∀ o ∈ #inst-calc(dof) qd &
    hasty(Γ, o, A, annot: #inst-calc(dof)) 
    &&<==> hasty(Γ, o, A, annot: #iter-calc(dof))
    &&
$

We note in particular that:

- #val-calc() inherits weakening and renaming from #dic:
  - If $ms("A")$ is stable under (input/output) weakening,
    then so is #val-calc(dael)
    -- in particular, if $ms("A")$ is a typed syntax,
    then so is #val-calc(dael)
  - If $ms("A")$ supports renaming,
    then so does #val-calc(dael)

- #val-calc(dael) 
  is in fact an expression syntax 
  (that is, #val-calc(dael)-substitutive, _not_ #iter-calc(dael)-substitutive!)
  whenever $dael$ is $#val-calc(dael)$-substitutive

- #inst-calc() inherits weakening and renaming from #dic:
  - If $dof$ is stable under (input/output) weakening,
    then so is #inst-calc(dof)
    -- in particular, if $dof$ is an operation family,
    then so is #inst-calc(dof)
  - If $dof$ supports renaming,
    then so does #inst-calc(dof)

- #inst-calc(dof) is not generally an expression syntax, but
  _is_ $#val-calc(dael)$-substitutive whenever $dof$ is $#val-calc(dael)$-substitutive.

- #val-calc() preserves subsets: 
  #space-imp(
    $dael ⊆ dael'$,
    $#val-calc(dael) ⊆ #val-calc($dael'$)$,
  )

- #inst-calc() preserves subsets:
  #space-imp(
    $dof ⊆ dof'$,
    $#inst-calc(dof) ⊆ #inst-calc($dof'$)$,
  )

- $#dic$ is $#val-calc(dael)$-substitutive, since $#val-calc(dael) ⊆ #iter-calc(dael)$

- $#iter-calc(dic) = dic$ and hence
  $#val-calc(dic) = dic$

- $#inst-calc($(ms("F"), #val-calc(ms("A")))$) = #inst-calc($(ms("F"), ms("A"))$)$

== Regions

#todo[Tag all substitution / weakening / label-weakening with appropriate language]

#import "../rules/haslb.typ": *

We now want to give a type theory for regions $r$. In particular, we will
- Give a type theory for _lexical SSA_ (#ssa-calc())
- Extend this to a type theory for _type-theoretic SSA_ (#gssa-calc())
- Noting that, syntactically, $#ssa-calc() ⊆ #gssa-calc()$,
  prove that
  $haslb(Γ, r, ms("L"), annot: #ssa-calc()) <==> haslb(Γ, r, ms("L"), annot: #gssa-calc())$
  for all (gramatically) well-formed #ssa-calc() regions $r$.

Our judgement in both cases will be of the form $haslb(Γ, r, ms("L"))$,
meaning that the region $r$
maps the context $Γ$ (corresponding to live variables on entry)
to the cocontext $ms("L")$ (corresponding to exit labels with parameter types).

Recall that our grammar
for lexical SSA (#ssa-calc()), repeated below in @lex-ssa-full,
defines the following four syntactic categories,
which we can roughly divide into two mutually-recursive groups:

- _Regions_ $r$, and _lists of named regions_ $L$ -- we call such lists _control-flow graphs (CFGs)_
- _Terminators_ $τ$, and _lists of branch targets_ $B$

#let lex-ssa-full = figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 2em),
      bnf(
        Prod($r$, {
          Or[$x = e seq r$][_assign_]
          Or[$(mb("x")) = e seq r$][_destructure_]
          Or[$τ$][_terminator_]
          Or[${ r } seq L$][_braces_]
        }),
        Prod($L$, {
          Or[$·$][]
          Or[$L seq gbr(lb("l"), x, {r})$][]
        }),
      ),

      bnf(
        Prod($τ$, {
          Or[$brb(lb("l"), e)$][_branch_]
          Or[$scase(e, B)$][_case_]
        }),
        Prod($B$, {
          Or[$·$][]
          Or[$B, sbr(lb("l₁"), x, brb(lb("l₂"), e))$][]
        }),
      ),
    )
  ],
  caption: [
    Grammar for lexical SSA with expressions and braces (#ssa-calc(iter-calc()))
  ],
  kind: image,
)

#lex-ssa-full <lex-ssa-full>

Our approach will be to:

- Give a grammar and type theory for a language of _regions_, #reg-calc(ms("E"), ms("T")),
  parametrized by _expressions_ $e ∈ ms("E")$ and _terminators_ $τ ∈ ms("T")$.

- Give a grammar and type theory for _terminators_ $#cond-calc(ms("E"))$:
  (potentially) conditional branches parametrized by expressions $e ∈ ms("E")$.

We will then define
$
  #ssa-calc(ms("E")) := #reg-calc(ms("E"), $#cond-calc(ms("E"))$)
$
while at the same time having a uniform framework for reasoning about different SSA variants.

In particular, our construction of #gssa-calc() by fusing the syntactic categories of terminators
and regions will be evidenced by the fact that
$
  #cond-calc(ms("E"))
  #h(2em) ⊆ #h(2em) #gssa-calc(ms("E"))
  #h(2em) = #h(2em) #reg-calc(ms("E"), gssa-calc(ms("E")))
$

We give a grammar for #reg-calc(ms("E"), ms("T")) below in @reg-grammar
-- this is precisely just the productions $r$ and $L$ from
the #ssa-calc() grammar in @lex-ssa-full:

#let fig-reg-grammar = figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 1em),
      bnf(Prod($r$, {
        Or[$x = e seq r$][_assign_]
        Or[$(mb("x")) = e seq r$][_destructure_]
        Or[$τ$][_terminator_]
        Or[${ r } seq L$][_braces_]
      })),
      bnf(
        Prod($L$, {
          Or[$·$][]
          Or[$L seq gbr(lb("l"), x, {r})$][]
        }),
      ),
    )
    \
  ],
  caption: [
    Grammar for $r ∈ #reg-calc(ms("E"), ms("T"))$
    parametrized by _expressions_ $e ∈ ms("E")$ and _terminators_ $τ ∈ ms("T")$
  ],
  kind: image,
)

#fig-reg-grammar <reg-grammar>


We give typing rules for #reg-calc(ms("E"), ms("T"))-judgements
#judgement-meaning(
  $haslb(Γ, r, ms("L"))$,
  ["Region $r ∈ ms("T")$ has takes context $Γ$ to cocontext $ms("L")$"],
  $klbrs(cal(K), L, ms("L"))$,
  ["The CFG $L$ maps polycontext $cal(K)$ to cocontext $ms("L")$"],
)
parametrized by a judgement
#judgement-meaning(
  $haslb(Γ, τ, ms("L"), annot: ms("T"))$,
  ["Terminator $τ ∈ ms("T")$ has takes context $Γ$ to cocontext $ms("L")$"],
)
in @cart-reg-rules below:

// Rules for ssa-calc(E, T)
#let r-assign = rule(
  name: "assign",
  $hasty(Γ, e, A)$,
  $haslb(#$Γ, x : A$, r, ms("L"))$,
  $haslb(#$Γ$, slet(x, e, r), ms("L"))$,
);
#let r-destruct = rule(
  name: [$"assign"_n$],
  $hasty(Γ, e, Π lb("T"))$,
  $haslb(#$Γ, lb("T")^mb("x")$, r, ms("L"))$,
  $haslb(#$Γ$, slet((mb("x")), e, r), ms("L"))$,
);
#let r-scope = rule(
  name: "scope",
  $haslb(Γ, r, #$ms("L"), ms("K")$)$,
  $klbrs(Γ csplat ms("K"), L, #$ms("L"), ms("K")$)$,
  $haslb(Γ, #${r} ; L$, ms("L"))$,
)
#let r-tm = rule(
  name: "tm",
  $haslb(Γ, τ, ms("L"), annot: ms("T"))$,
  $haslb(Γ, τ, ms("L"))$,
);
#let r-lb-nil = rule(
  name: "lb-nil",
  $klbrs(cal(K), ·, ·)$,
);
#let r-lb-cons = rule(
  name: "lb-cons",
  $ksbrs(cal("K"), L, ms("L"))$,
  $haslb(#$Γ, x : A$, r, ms("L"))$,
  $klbrs(#$cal("K"), clty(lb("k"), Γ, A)$, #$K, sbr(lb("k"), x, r)$, ms("L"))$,
);has

#let fig-haslb-reg = figure(
  [
    #rule-set(
      declare-rule(r-assign, label: <r-cart-assign>),
      declare-rule(r-destruct, label: <r-cart-reg-destruct>),
      declare-rule(r-scope, label: <r-cart-reg-scope>),
      declare-rule(r-tm, label: <r-cart-tm>),
      declare-rule(r-lb-nil),
      declare-rule(r-lb-cons),
    )
    \
  ],
  caption: [Typing rules for #reg-calc(ms("E"), ms("T"))],
)

#fig-haslb-reg <cart-reg-rules>

In particular,

- We type assignments using @r-cart-assign.
  As for expressions, we require $x ∉ Γ$ to be fresh.

- We type destructurings using @r-cart-reg-destruct.
  As for expressions, we require each variable in $mb("x")$ to be fresh.

- We inherit typing for terminators from $ms("T")$ using @r-cart-tm

- We type braces using @r-cart-reg-scope,
  where the polycontext $Γ csplat ms("K")$ broadcasts $Γ$ along the cocontext $ms("K")$.

As for expressions, we can verify that our type system respects both (variable) _weakening_
and _label weakening_ by induction:

#lemma(name: "Weakening")[
  If $ms("E")$ and $ms("T")$ are stable under weakening,
  then so is #reg-calc(ms("E"), ms("T"))
  -- i.e. for all $Γ ⊑ Δ$,
  $
    haslb(Δ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, r, ms("L"))
  $
  where we say that $ms("E")$ and $ms("T")$ are stable under weakening when
  - For all $Γ ⊑ Δ$, $hasty(Δ, e, A)$ implies $hasty(Γ, e, A)$.
  - For all $Γ ⊑ Δ$, $haslb(Δ, τ, ms("L"), annot: ms("T"))$ implies
    $haslb(Γ, τ, ms("L"), annot: ms("T"))$.
]

#lemma(name: "Label Weakening")[
  If $ms("T")$ is stable under label weakening,
  then so is #reg-calc(ms("E"), ms("T"))
  -- i.e. for all $ms("L") sle() ms("K")$,
  $
    haslb(Γ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, r, ms("K"))
  $
  where we say that $ms("T")$ is stable under label weakening when
  - For all $ms("L") sle() ms("K")$,
    $haslb(Γ, τ, ms("L"), annot: ms("T"))$ implies
    $haslb(Γ, τ, ms("K"), annot: ms("T"))$.
]

To state _substitution_, intuitively,
we need both our grammar of _expressions_ $ms("E")$
and our grammar of _terminators_ $ms("T")$ to be appropriately closed under substitution
-- just like how defining capture-avoiding substitution on expressions $e ∈ #dic$
requires defining substitution for atomic expressions $α ∈ dael$ and functions $f ∈ dfnl$.
In particular, we give a definition of capture-avoiding substitution on regions
in @cap-avoid-reg-subst-rules below:

#figure(
  [
    $
              γ · (slet(x, e, r)) & := (slet(x, γ ·_ms("E") e, γ · r)) //
                                                     & #h(1em) & "(choosing " x ∉ fsup(γ)")" \
      γ · (slet((mb("x")), e, r)) & := (slet((mb("x")), γ ·_ms("E") e, γ · r)) //
                                                     &         & "(choosing " mb("x") ∩ fsup(γ) = ∅")" \
                            γ · τ & := γ ·_ms("T") τ \
    $
    $
      & γ · ({r} seq L) := {γ · r} seq (γ · L) "where" \
      & #h(2em) γ · (·_L) := (·_L), \
      & #h(2em) γ · (L seq sbr(lb("l"), x, r)) := (γ · L, sbr(lb("l"), x, γ · r))
        #h(2em)
        "(choosing " x ∉ fsup(γ)")"
    $
    \
    where we are given
    \
    $
      (·_ms("E")) & : substs(ms("E")') → ms("E") → ms("E") & #h(3em) & "(substitution on expressions)" \
      (·_ms("T")) & : substs(ms("E")') → ms("T") → ms("T") &         & "(substitution on terminators)"
    $
    for some expression grammar $vset ⊆ ms("E")'$.
    \
    \
  ],
  caption: [
    Capture-avoiding substitution on regions $r ∈ #reg-calc(ms("E"), ms("T"))$
  ],
) <cap-avoid-reg-subst-rules>

We can then state substitution for #reg-calc(ms("E"), ms("T")) as follows:
#lemma(name: "Substitution")[
  If $ms("E")$ and $ms("T")$ are stable under substitution,
  then so is #reg-calc(ms("E"), ms("T"))
  -- i.e. for all $issubst(Γ, γ, Δ)$,
  $
    haslb(Δ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, γ ·_ms("E") r, ms("L"))
  $
  where we say that $ms("E")$ and $ms("T")$ are stable under substitution when
  - For all $issubst(Γ, γ, Δ)$ and $hasty(Δ, e, A)$,
    we have $hasty(Γ, γ ·_ms("E") e, A)$.
  - For all $issubst(Γ, γ, Δ)$ and $haslb(Δ, τ, ms("L"), annot: ms("T"))$,
    we have $haslb(Γ, γ ·_ms("T") τ, ms("L"), annot: ms("T"))$.
]

Note that we've snuck in a little additional generality here:
- We never actually assumed that $ms("E") = #dic$ for some $dof$
  -- $#dael$, for example, would also be a perfectly valid choice
- Our substitutions are of type $γ ∈ substs(ms("E")')$ -- again, we never assumed that
  $ms("E")' = ms("E")$ _or_ that $ms("E")' = #dic$,
  only that $vset ⊆ ms("E"')$.

  In particular, this means that our substitution lemma is parametric not only on
  typing rules for expressions $ms("E")$ and terminators $ms("T")$,
  but also on typing rules for a potentially different expression grammar $ms("E")'$
  (which, via the rules in @cart-iter-subst-rules, give us typing rules for substitutions
  $γ ∈ substs(ms("E")')$).

We can recover our lexical SSA language $#ssa-calc()$ from the introduction,
extended with additional terminators $τ ∈ ms("T")$, by taking
$
  #ssa-calc(ms("E"), ms("T"))
  := #reg-calc(ms("E"), $#cond-calc(ms("E")) ∪ ms("T")$)
$
Here, we define $#cond-calc(ms("E"))$ to be the language of _(potentially) conditional branches_,
given in @br-grammar below:
#let fig-br-grammar = figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 2em),
      bnf(Prod($u$, {
        Or[$brb(lb("l"), e)$][_branch_]
      })),
      bnf(Prod($τ$, {
        Or[$j$][_jump_]
        Or[$scase(e, K)$][_cases_]
      })),
      bnf(
        Prod($K$, {
          Or[$·$][]
          Or[$K seq gbr(lb("l"), x, j)$][]
        }),
      ),
    )
    \
  ],
  caption: [
    Grammar
    for _unconditional branches_ $u ∈ #br-calc(ms("E"))$
    and _conditional branches_ $τ ∈ #cond-calc(ms("E"), ms("U"))$
    parametrized by _expressions_ $e ∈ ms("E")$ and _jumps_ $j ∈ ms("U")$.
    //
    We define $#cond-calc(ms("E")) := #cond-calc(ms("E"), br-calc(ms("E")))$.
  ],
  kind: image,
)

#fig-br-grammar <br-grammar>

We may give typing rules for #cond-calc(ms("E"), ms("U")) in @cart-br-rules below:

// Rules for br-calc(E)
#let r-cond-tm = rule(
  name: "tm",
  $haslb(Γ, j, ms("L"), annot: ms("U"))$,
  $haslb(Γ, j, ms("L"))$,
);
#let r-cond-case = rule(
  name: "case",
  $hasty(Γ, e, Σ lb("L"))$,
  $ksbrs(Γ csplat lb("L"), K, ms("K"))$,
  $haslb(Γ, scase(e, K), ms("K"))$,
);
#let r-case-nil = rule(
  name: "case-nil",
  $ksbrs(cal(L), ·, ·)$,
);
#let r-case-cons = rule(
  name: "case-cons",
  $ksbrs(cal(L), K, ms("K"))$,
  $haslb(#$Γ, x : A$, brb(lb("k"), e), ms("K"))$,
  $ksbrs(#$cal("L"), clty(lb("l"), Γ, A)$, #$K, sbr(lb("l"), x, brb(lb("k"), e))$, ms("K"))$,
);

#let fig-haslb-br = figure(
  [
    #rule-set(
      declare-rule(r-cond-tm),
      declare-rule(r-cond-case),
      declare-rule(r-cond-case),
      declare-rule(r-case-nil),
      declare-rule(r-case-cons),
    )
    \
  ],
  caption: [
    Typing rules for #cond-calc(ms("E"), ms("U")) and #br-calc(ms("E")).
    We define $#cond-calc(ms("E")) := #cond-calc(ms("E"), br-calc(ms("E")))$.
  ],
)

#fig-haslb-br <cart-br-rules>

Weakening and label-weakening can be stated as follows:
#lemma(name: "Weakening")[
  If $ms("E")$ and $ms("U")$ are stable under weakening,
  then so is #cond-calc(ms("E"), ms("U"))
  -- i.e. for all $Γ ⊑ Δ$,
  $
    haslb(Δ, τ, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, τ, ms("L"))
  $
  where we say that $ms("E")$ and $ms("U")$ are stable under weakening when
  - For all $Γ ⊑ Δ$, $hasty(Δ, e, A, annot: ms("E"))$ implies $hasty(Γ, e, A, annot: ms("E"))$.
  - For all $Γ ⊑ Δ$, $haslb(Δ, j, ms("L"), annot: ms("U"))$ implies
    $haslb(Γ, j, ms("L"), annot: ms("U"))$.
]

#lemma(name: "Label Weakening")[
  If $ms("T")$ is stable under label weakening,
  then so is #cond-calc(ms("E"), ms("U"))
  -- i.e. for all $ms("L") sle() ms("K")$,
  $
    haslb(Γ, τ, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, τ, ms("K"))
  $
  where we say that $ms("U")$ is stable under label weakening when
  - For all $ms("L") sle() ms("K")$,
    $haslb(Γ, j, ms("L"), annot: ms("U"))$ implies
    $haslb(Γ, j, ms("K"), annot: ms("U"))$.
]

Likewise, we define capture-avoiding substitution for #cond-calc(ms("E"), ms("U")) by
structural recursion in @cap-avoid-cond-subst-rules below:

#figure(
  [
    #eqn-set(
      $γ · j = γ ·_ms("U") j$,
      $$,
    )
    $
      & γ · (scase(e, K)) := scase(γ ·_ms("E") e, γ · K) "where" \
      & #h(2em) γ · (·_K) := (·_K), \
      & #h(2em) γ · (K seq sbr(lb("l"), x, j)) := (γ · K, sbr(lb("l"), x, γ ·_ms("U") j))
        #h(2em)
        "(choosing " x ∉ fsup(γ)")"
    $
    \
    where we are given
    \
    $
      (·_ms("E")) & : substs(ms("E")') → ms("E") → ms("E") & #h(3em) & "(substitution on expressions)" \
      (·_ms("U")) & : substs(ms("E")') → ms("U") → ms("U") &         & "(substitution on jumps)"
    $
    for some expression grammar $vset ⊆ ms("E")'$.
    \
    \
  ],
  caption: [
    Capture-avoiding substitution on regions $r ∈ #reg-calc(ms("E"), ms("U"))$
  ],
) <cap-avoid-cond-subst-rules>

We can then state the substitution lemma as follows:
#lemma(name: "Substitution")[
  If $ms("E")$ and $ms("U")$ are stable under substitution,
  then so is #cond-calc(ms("E"), ms("U"))
  -- i.e. for all $issubst(Γ, γ, Δ)$ and $haslb(Δ, τ, ms("L"))$,
  $ haslb(Γ, γ · τ, ms("L")) $
  where we say that $ms("E")$ and $ms("U")$ are stable under substitution when
  - For all $issubst(Γ, γ, Δ)$ and $hasty(Δ, e, A, annot: ms("E"))$,
    we have $hasty(Γ, γ ·_ms("E") e, A, annot: ms("E"))$.
  - For all $issubst(Γ, γ, Δ)$ and $haslb(Δ, j, ms("L"), annot: ms("U"))$,
    we have $haslb(Γ, γ ·_ms("U") j, ms("L"), annot: ms("U"))$.
]

On the other hand, #br-calc(ms("E")) requires only a single typing rule for unconditional jumps:

#let r-br = rule(
  name: "br",
  $lbcwk(lty(lb("l"), A), ms("L"))$,
  $hasty(Γ, e, A, annot: ms("E"))$,
  $haslb(Γ, brb(lb("l"), e), ms("L"), annot: #br-calc(ms("E")))$,
);
$
  #declare-rule(r-br)
$

We can view #br-calc(ms("E")) as the minimal "lifting" an of expression language $ms("E")$ into a
region language. In particular, defining
$
  γ · (brb(lb("l"), e)) := brb(lb("l"), γ ·_ms("E") e)
$
we satisfy

#lemma(name: "Weakening")[
  If $ms("E")$ is stable under weakening,
  then so is #br-calc(ms("E"))
  -- i.e. for all $Γ ⊑ Δ$,
  $
    haslb(Δ, u, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, u, ms("L"))
  $
  where we say that $ms("E")$ is stable under weakening when
  - For all $Γ ⊑ Δ$, $hasty(Δ, e, A, annot: ms("E"))$ implies $hasty(Γ, e, A, annot: ms("E"))$.
]

#lemma(name: "Label Weakening")[
  #br-calc(ms("E")) is stable under label weakening
  -- i.e. for all $ms("L") sle() ms("K")$,
  $
    haslb(Γ, u, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, u, ms("K"))
  $
]

#lemma(name: "Substitution")[
  If $ms("E")$ is stable under substitution,
  then so is #br-calc(ms("E"))
  -- i.e. for all $issubst(Γ, γ, Δ)$,
  $
    haslb(Δ, u, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, γ · u, ms("L"))
  $
  where we say that $ms("E")$ is stable under substitution when
  - For all $issubst(Γ, γ, Δ)$ and $hasty(Δ, e, A, annot: ms("E"))$,
    we have $hasty(Γ, γ ·_ms("E") e, A, annot: ms("E"))$.
]

It follows that we can combine our results for #reg-calc() and #cond-calc() to derive results for
#ssa-calc(), where we define
$
  #ssa-calc(ms("E"), ms("T")) := #reg-calc(ms("E"), $#cond-calc(ms("E")) ∪ ms("T")$)
$

In particular, we have:

#lemma(name: "Weakening")[
  If $ms("E")$ and $ms("T")$ are stable under weakening,
  then so is #ssa-calc(ms("E"), ms("T"))
  -- i.e. for all $Γ ⊑ Δ$,
  $
    haslb(Δ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, r, ms("L"))
  $
  where we say that $ms("E")$ and $ms("T")$ are stable under weakening when
  - For all $Γ ⊑ Δ$, $hasty(Δ, e, A)$ implies $hasty(Γ, e, A)$.
  - For all $Γ ⊑ Δ$, $haslb(Δ, τ, ms("L"), annot: ms("T"))$ implies
    $haslb(Γ, τ, ms("L"), annot: ms("T"))$.
]

#lemma(name: "Label Weakening")[
  If $ms("T")$ is stable under label weakening,
  then so is #ssa-calc(ms("E"), ms("T"))
  -- i.e. for all $ms("L") sle() ms("K")$,
  $
    haslb(Γ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, r, ms("K"))
  $
  where we say that $ms("T")$ is stable under label weakening when
  - For all $ms("L") sle() ms("K")$,
    $haslb(Γ, τ, ms("L"), annot: ms("T"))$ implies
    $haslb(Γ, τ, ms("K"), annot: ms("T"))$.
]

#lemma(name: "Substitution")[
  If $ms("E")$ and $ms("T")$ are stable under substitution,
  then so is #ssa-calc(ms("E"), ms("T"))
  -- i.e. for all $issubst(Γ, γ, Δ)$,
  $
    haslb(Δ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, γ · r, ms("L"))
  $
  where we say that $ms("E")$ and $ms("T")$ are stable under substitution when
  - For all $issubst(Γ, γ, Δ)$ and $hasty(Δ, e, A)$,
    we have $hasty(Γ, γ ·_ms("E") e, A)$.
  - For all $issubst(Γ, γ, Δ)$ and $haslb(Δ, τ, ms("L"), annot: ms("T"))$,
    we have $haslb(Γ, γ ·_ms("T") τ, ms("L"), annot: ms("T"))$.
]

In particular, substitution therefore holds for lexical SSA
_with expressions_
as defined in the introduction
-- $#ssa-calc(dic))$.
However, we also want to reason about lexical _standard SSA_
-- i.e., SSA in which each assignment performs only a single primitive instruction,
as we might find in a typical compiler.

We can then define standard lexical SSA
#footnote[
  Note that there is also a more strict variant of SSA which does not allow a raw value $v$
  (and in particular, a constant $α$ or variable $x$)
  to appear directly on the RHS of an instruction.
  //TODO: we will study this variant later on.
]
by taking
$
  #standard-ssa(dof) := #ssa-calc(inst-calc(dof))
$

#todo[_In general_, when we write $ms("S") ⊆ ms("S")'$ for some _typed syntax_, we mean (lore)]

We inherit typing for $#val-calc()$ and $#inst-calc()$ from $#iter-calc()$
-- implying that we also inherit both _weakening_ and _subtyping_. More formally,

- #todo[Can use cast for #val-calc()]

- #todo[Thing for #iter-calc()]


#todo[Be explicit here -- for #val-calc() case, this introduces the _empty language_]

We can then define standard lexical SSA as
$#standard-ssa(dof) := #ssa-calc(inst-calc(dof))$.
While the resulting language supports weakening and label-weakening via the above lemmas,
we do _not_ support substitution, as #inst-calc(dof) is not generally stable under substitution.

#todo[We _do_, however, support _renaming_: define below]

#todo[Segue to label-renaming]

We can also perform _label renaming_ in #ssa-calc(ms("E")).
In particular,

- We define a label-renaming $ρ ∈ lrens$ to be a finitely-supported injection from labels to labels,
  where we define the support $fsup(ρ)$ of a function $ρ : lset → lset$ as follows:
  $
    fsup(ρ) := { lb("l") ∈ lset | ρ(lb("l")) ≠ lb("l") }
  $

- We define the action of a label-renaming $ρ ∈ lrens$ on regions $r ∈ #reg-calc(ms("E"), ms("T"))$
  by structural recursion as follows:
  $
            ρ · (slet(x, e, r)) & := slet(x, e, ρ · r) \
    ρ · (slet((mb("x")), e, r)) & := slet((mb("x")), e, ρ · r) \
                          ρ · τ & := ρ ·_ms("T") τ \
  $
  $
    & ρ · ({r} seq L) := {ρ · r} seq (ρ · L) "where" \
    & #h(2em) ρ · (·_L) := (·_L), \
    & #h(2em) ρ · (L seq gbr(lb("l"), x, {r})) := (ρ · L, gbr(lb("l"), x, ρ · r))
      #h(2em)
      "(choosing " lb("l") ∉ fsup(ρ)")"
  $
  where we are given
  $
    ρ ·_ms("T") & : lrens → ms("T") → ms("T")
  $
  defining the action of label-renamings on terminators $τ ∈ ms("T")$.

  Note that we can always choose $lb("l") ∉ fsup(ρ)$ since $fsup(ρ)$ is finite and names of
  bound labels are quotiented up to α-equivalence.

  Likewise, we define the action of a label-renaming $ρ ∈ lrens$ on terminators
  $τ ∈ #cond-calc(ms("E"), ms("U"))$ by structural recursion as follows:
  $
    & ρ · j := ρ ·_ms("U") j \
    & ρ · (scase(e, K)) := scase(e, ρ · K) "where" \
    & #h(2em) ρ · (·_K) := (·_K), \
    & #h(2em) ρ · (K seq sbr(lb("l"), x, j)) := (ρ · K, sbr(lb("l"), x, ρ ·_ms("U") j))
      #h(2em)
      "(choosing " lb("l") ∉ fsup(ρ)")"
  $
  where we are given
  $
    ρ ·_ms("U") & : lrens → ms("U") → ms("U")
  $
  defining the action of label-renamings on jumps $j ∈ ms("U")$.

  Finally, we define the action of a label-renaming $ρ ∈ lrens$ on unconditional branches
  $u ∈ #br-calc(ms("E"))$ pointwise:
  $
    ρ · (brb(lb("l"), e)) := brb(ρ(lb("l")), e)
  $

- We may then state _label-renaming_ for
  #reg-calc(ms("E"), ms("T")), #cond-calc(ms("E"), ms("U")), #br-calc(ms("E")) as follows:
  #lemma(name: [Label Renaming (#reg-calc(ms("E"), ms("T"))])[
    If $ms("T")$ is stable under label-renaming,
    then so is #reg-calc(ms("E"), ms("T"))
    -- i.e. for all $ρ ∈ lrens$,
    $
      haslb(Γ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, ρ · r, ms("L"))
    $
    where we say that $ms("T")$ is stable under label-renaming when
    - For all $ρ ∈ lrens$ and $haslb(Γ, τ, ms("L"), annot: ms("T"))$,
      we have $haslb(Γ, ρ ·_ms("T") τ, ms("L"), annot: ms("T"))$.
  ]

  #lemma(name: [Label Renaming (#cond-calc(ms("E"), ms("U"))])[
    If $ms("U")$ is stable under label-renaming,
    then so is #cond-calc(ms("E"), ms("U"))
    -- i.e. for all $ρ ∈ lrens$,
    $
      haslb(Γ, τ, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, ρ · τ, ms("L"))
    $
    where we say that $ms("U")$ is stable under label-renaming when
    - For all $ρ ∈ lrens$ and $haslb(Γ, j, ms("L"), annot: ms("U"))$,
      we have $haslb(Γ, ρ ·_ms("U") j, ms("L"), annot: ms("U"))$.
  ]

  #lemma(name: [Label Renaming (#br-calc(ms("E"))])[
    #br-calc(ms("E")) is stable under label-renaming
    -- i.e. for all $ρ ∈ lrens$,
    $
      haslb(Γ, u, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, ρ · u, ms("L"))
    $
  ]

It follows that we have:
#lemma(name: [Label Renaming (#ssa-calc(ms("E"), ms("T"))])[
  If $ms("T")$ is stable under label-renaming,
  then so is #ssa-calc(ms("E"), ms("T"))
  -- i.e. for all $ρ ∈ lrens$,
  $
    haslb(Γ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, ρ · r, ms("L"))
  $
  where we say that $ms("T")$ is stable under label-renaming when
  - For all $ρ ∈ lrens$ and $haslb(Γ, τ, ms("L"), annot: ms("T"))$,
    we have $haslb(Γ, ρ ·_ms("T") τ, ms("L"), annot: ms("T"))$.
]

#todo[
  Modified segue: #standard-ssa(dof)
  is embedded in a bigger language #ssa-calc(dic)) which lets us do substitution]

#todo[What's the bigger language which lets us do _label-substitution_?]

On the other hand, just as substitution allows us to rewrite _data-flow_,
to rewrite _control-flow_, it helps to be able
to perform _label-substitution_ -- i.e., to replace _jumps_ to a label $lb("l")$
with the body of that label
(rather than simply with a jump to another label).

Our grammar for regions #reg-calc(ms("E"), ms("T")) is compatible with replacing entire
_terminators_ $τ ∈ ms("T")$ with a region $r ∈ #reg-calc(ms("E"), ms("T"))$
(this is, in fact, the real motivation for introducing braces in the first place).
So whether we can perform label-substitution
depends on what our grammar of terminators looks like.

#ssa-calc(ms("E")), however, does _not_ allow us to perform label-substitution, since in particular
the branches of a case-statement $scase(e, B)$ can only be unconditional branches $brb(lb("l"), e)$,
rather than arbitrary regions.

One way to remedy this is to fuse the syntactic categories of
_terminators_ $τ$, _regions_ $r$, and unconditional branches $u$ together.

In terms of syntax, what we're doing is allowing the branches of a case-statment to
be arbitrary, anonymous regions, rather than just unconditional branches, yielding an
extended language $#ssa-calc(ms("E"), ms("T")) ⊆ #gssa-calc(ms("E"), ms("T"))$.
Phrased in this way, it's easy to see that we add no additional expressive power:
we can always name such anonymous regions with a label and jump to them instead,
recovering an ordinary #ssa-calc(ms("E"), ms("T")) program.
We give a grammar for #gssa-calc(ms("E"), ms("T")) in @gssa-grammar below.

#let fig-gssa-grammar = figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 1em),
      bnf(Prod($r$, {
        Or[$x = e seq r$][_assign_]
        Or[$(mb("x")) = e seq r$][_destructure_]
        Or[$brb(lb("l"), e)$][_branch_]
        Or[$scase(e, L)$][_case_]
        Or[$τ$][_terminator_]
        Or[${ r } seq L$][_braces_]
      })),
      bnf(
        Prod($L$, {
          Or[$·$][]
          Or[$gbr(lb("l"), x, {r}) seq L$][]
        }),
      ),
    )
    \
  ],
  caption: [Grammar for #gssa-calc(ms("E"), ms("T"))],
  kind: image,
)

#fig-gssa-grammar <gssa-grammar>

We note in particular that we have
(identifying a language with its set of syntactically-well formed terms)
$
  ms("T") ⊆ #gssa-calc(ms("E"), ms("T"))
  = #ssa-calc(ms("E"), $#gssa-calc(ms("E"), ms("T"))$)
$
As we would expect from this equation,
we inherit typing rules from #reg-calc() and #cond-calc() directly
-- in particular, the typing rules for #gssa-calc(ms("E"), ms("T"))
are given in @cart-gssa-rules.

#fig-haslb-gssa <cart-gssa-rules>

Weakening and label-weakening generalize straightforwardly to #gssa-calc(ms("E"), ms("T")):

#lemma(name: "Weakening")[
  If $ms("E")$ and $ms("T")$ are stable under weakening,
  then so is #gssa-calc(ms("E"), ms("T"))
  -- i.e. for all $Γ ⊑ Δ$,
  $
    haslb(Δ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, r, ms("L"))
  $
  where we say that $ms("E")$ and $ms("T")$ are stable under weakening when
  - For all $Γ ⊑ Δ$, $hasty(Δ, e, A)$ implies $hasty(Γ, e, A)$.
  - For all $Γ ⊑ Δ$, $haslb(Δ, τ, ms("L"), annot: ms("T"))$ implies
    $haslb(Γ, τ, ms("L"), annot: ms("T"))$.
]

#lemma(name: "Label Weakening")[
  If $ms("T")$ is stable under label weakening,
  then so is #gssa-calc(ms("E"), ms("T"))
  -- i.e. for all $ms("L") sle() ms("K")$,
  $
    haslb(Γ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, r, ms("K"))
  $
  where we say that $ms("T")$ is stable under label weakening when
  - For all $ms("L") sle() ms("K")$,
    $haslb(Γ, τ, ms("L"), annot: ms("T"))$ implies
    $haslb(Γ, τ, ms("K"), annot: ms("T"))$.
]

Likewise, we may define capture-avoiding substitution for #gssa-calc(ms("E"), ms("T"))
to respect the equation $#gssa-calc(ms("E"), ms("T"))
= #ssa-calc(ms("E"), $#gssa-calc(ms("E"), ms("T"))$)$ as follows:

#figure(
  [
    $
              γ · (slet(x, e, r)) & := slet(x, (γ ·_ms("E") e), (γ · r))
                                    "choosing" x ∉ fsup(γ) \
      γ · (slet((mb("x")), e, r)) & := slet((mb("x")), (γ ·_ms("E") e), (γ · r))
                                    "choosing" mb("x") ∉ fsup(γ) \
            γ · (brb(lb("l"), e)) & := brb(lb("l"), (γ ·_ms("E") e)) \
                γ · (scase(e, L)) & := scase(γ ·_ms("E") e, γ · L) \
                            γ · τ & := γ ·_ms("T") τ \
                γ · ({ r } seq L) & := { γ · r } seq (γ · L)
    $
    \
    where
    $
                             γ · (·_L) & := (·_L), \
      γ · (L seq gbr(lb("l"), x, {r})) & := (γ · L, gbr(lb("l"), x, γ · {r}))
                                         #h(2em)
                                         "(choosing " x ∉ fsup(γ)")"
    $
    \
    where we are given
    \
    $
      (·_ms("E")) & : substs(ms("E")') → ms("E") → ms("E") & #h(3em) & "(substitution on expressions)" \
      (·_ms("T")) & : substs(ms("E")') → ms("T") → ms("T") &         & "(substitution on terminators)"
    $
    for some expression grammar $vset ⊆ ms("E")'$.
    \
    \
  ],
  caption: [
    Capture-avoiding substitution on regions $r ∈ #gssa-calc(ms("E"), ms("T"))$
  ],
)

allowing us to state _the substitution lemma_ for #gssa-calc(ms("E"), ms("T")) as follows:

#lemma(name: "Substitution")[
  If $ms("E")$ and $ms("T")$ are stable under substitution,
  then so is #gssa-calc(ms("E"), ms("T"))
  -- i.e. for all $issubst(Γ, γ, Δ)$,
  $
    haslb(Δ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, γ · r, ms("L"))
  $
  where we say that $ms("E")$ and $ms("T")$ are stable under substitution when
  - For all $issubst(Γ, γ, Δ)$ and $hasty(Δ, e, A)$,
    we have $hasty(Γ, γ ·_ms("E") e, A)$.
  - For all $issubst(Γ, γ, Δ)$ and $haslb(Δ, τ, ms("L"), annot: ms("T"))$,
    we have $haslb(Γ, γ ·_ms("T") τ, ms("L"), annot: ms("T"))$.
]

We can now define _label-substitution_ as follows:

- A _region-with-hole_ #hgssa-calc(ms("E"), ms("T"))
  is a pair $(x, r) ∈$ of a variable $x ∈ vset$ and a
  region $r ∈ #gssa-calc(ms("E"), ms("T"))$ quotiented up to α-equivalence:
  $
    (x, r) ∼ (y, [y slash x]r)
  $

  Given a region-with-hole $holescript(r)$, we define $holescript(r)(e)$ to be given by
  $
    (x, r)(e) := (elet(x, e, r))
  $

- A _label-substitution_ $ℓ ∈ lsubsts(#gssa-calc(ms("E"), ms("T")))$ is a finitely-supported map from labels to
  regions-with-holes, where we define the support $fsup(ℓ)$ of a function
  $ℓ : lset → #hgssa-calc(ms("E"), ms("T"))$
  as follows:
  $
    fsup(ℓ) := { lb("l") ∈ lset | ℓ(lb("l")) ≠ (x, brb(lb("l"), x)) }
  $

- We define the action of a label-substitution $ℓ ∈ lsubsts(#gssa-calc(ms("E"), ms("T")))$
  on regions $r ∈ #gssa-calc(ms("E"), ms("T"))$ by structural recursion as follows:

  #figure(
    [
      $
                ℓ · (slet(x, e, r)) & := slet(x, e, ℓ · r) \
        ℓ · (slet((mb("x")), e, r)) & := slet((mb("x")), e, ℓ · r) \
              ℓ · (brb(lb("l"), e)) & := ℓ(lb("l"))(e) \
                  ℓ · (scase(e, L)) & := scase(e, ℓ · L) \
                              ℓ · τ & := ℓ ·_ms("T") τ \
                  ℓ · ({ r } seq L) & := { ℓ · r } seq (ℓ · L)
      $
      where
      $
                               ℓ · (·_L) & := (·_L), \
        ℓ · (L seq gbr(lb("l"), x, {r})) & := (ℓ · L, gbr(lb("l"), x, ℓ · {r}))
                                           #h(2em)
                                           "(choosing " lb("l") ∉ fsup(ℓ)")"
      $
      where we are given
      $
        ℓ ·_ms("T") & : lsubsts(#gssa-calc(ms("E"), ms("T"))) → ms("T") → ms("T")
      $
      defining the action of label-substitutions on terminators $τ ∈ ms("T")$.
      \
    ],
  )

- We give a typing rule for label-substitution in @gssa-label-subst-rule below:

  #let r-lsubst-nil = rule(
    name: "lsubst-nil",
    $lbsubst(·, ℓ, ms("K"))$,
  );

  #let r-lsubst-cons = rule(
    name: "lsubst-cons",
    $lbsubst(cal("L"), ℓ, ms("K"))$,
    $haslb(#$Γ, x : A$, ℓ(lb("l"))(x), ms("L"))$,
    $x ∉ ms("fv")(ℓ(lb("l")))$,
    $haslb(#$cal("L"), clty(ℓ, Γ, A)$, ℓ, ms("K"))$,
  );

  #figure(
    [
      #rule-set(
        declare-rule(r-lsubst-nil),
        declare-rule(r-lsubst-cons),
      )
    ],
    caption: [Typing Rule for Label-Substitution in #gssa-calc(ms("E"), ms("T"))],
  ) <gssa-label-subst-rule>

We can now state the _label-substitution lemma_ for #gssa-calc(ms("E"), ms("T")) as follows:

#lemma(name: "Label Substitution")[
  If $ms("T")$ is stable under label-substitution,
  then so is #gssa-calc(ms("E"), ms("T"))
  -- i.e. for all $lbsubst(cal("L"), ℓ, ms("K"))$,
  $
    haslb(Γ, r, ms("L")) #h(3em) ==> #h(3em) haslb(Γ, ℓ · r, ms("K"))
  $
  where we say that $ms("T")$ is stable under label-substitution when
  - For all $lbsubst(cal("L"), ℓ, ms("K"))$ and $haslb(Γ, τ, ms("L"), annot: ms("T"))$,
    we have $haslb(Γ, ℓ ·_ms("T") τ, ms("K"), annot: ms("T"))$.
]

#todo[
  An expression syntax
]

#todo[
  Region language definition:

  - _region syntax_:
    - $ms("S") : ms("X") sfn ms("Y")$ where
    - $ms("X"), ms("Y")$ equipped with (distinguished) _renaming (left) action_ of 
      (distinguished) _renaming monoid_ on inputs $|ms("X")|$
    - $|S|$ equipped with (distinguished) renaming (left) action by same monoid
    - Typing compatible with _renaming_: 
      $hasty(X, s, Y, annot: ms("S")) <==> hasty(ρ · X, ρ · s, ρ · Y, annot: ms("S"))$
      -- note we rename outputs as well!
    - $ms("Y")$ equipped with (distinguished) _label renaming (right) action_ of 
      (distinguished) _label renaming monoid_ on outputs $|ms("Y")|$
      -- respects weakening
    - $|S|$ equipped with (distinguished) renaming (right) action by same monoid
    - Typing compatible with output renaming: 
      $hasty(X, s, Y, annot: ms("S")) <==> hasty(X, s · ρ, Y · ρ, annot: ms("S"))$

    Typical cases:
    - $ms("S") : sctx(ms("X")) sfn slctx(ms("Y"))$ (context as LHS, cocontext as RHS)
      (THIS IS US)
      - renaming action by $vset ↪_ms("fin") vset$ finitely supported injections
        -- note this is the identity on RHS since no variables $x ∈ vset$ in cocontexts
      - label renaming action by $lset ↪_ms("fin") lset$ finitely supported injections
        on labels
    - $ms("S") : sctx(ms("X")) sfn sdnf(ms("Y"))$ (context as LHS, polycontext as RHS)
      - renaming action by $vset ↪_ms("fin") vset$ finitely supported injections
        -- _not_ the identity on the RHS since polycontexts have variables $x ∈ vset$!
      - label renaming action by $lset ↪_ms("fin") lset$ finitely supported injections
        on labels
]

#todo[
  Note region syntax =/=> expression syntax -- it's just SSA is both as action by renaming on
  contexts is identity.

  Later, when we study program fragments with polycontext output, we'll want to rename outputs
  when we rename inputs -- so a region syntax which is _not_ an expression syntax;
  or rather, being an expression syntax is a _separate_ property.
]

== Typing

So far, we've defined numerous languages and associated typing judgements -- to recap:
#judgement-meaning(
  $hasty(Γ, e, A, annot: #dic)$,
  ["Expression $e ∈ #dic$ has type $A$ in $Γ$"],
  $haslb(Γ, r, ms("L"), annot: #gssa-calc(ms("E"), ms("T")))$,
  ["Region $r ∈ #gssa-calc(ms("E"), ms("T"))$ takes context $Γ$ to cocontext $ms("L")$"],
  $haslb(Γ, r, ms("L"), annot: #reg-calc(ms("E"), ms("T")))$,
  ["Region $r ∈ #reg-calc(ms("E"), ms("T"))$ takes context $Γ$ to cocontext $ms("L")$"],
  $haslb(Γ, τ, ms("L"), annot: #cond-calc(ms("E"), ms("T")))$,
  ["Terminator $τ ∈ #cond-calc(ms("E"), ms("T"))$ takes context $Γ$ to cocontext $ms("L")$"],
)
We also defined auxiliary judgements:
#judgement-meaning(
  $istup(Γ, E, lb("T"), annot: #dic)$,
  ["The fields $(E)$ have product type $Π lb("T")$ in $Γ$"],
  $kebrs(cal(K), M, A, annot: #dic)$,
  ["The case-expression branches $M$ map inputs $cal(K)$ to output $A$"],
  $klbrs(cal(K), L, A, annot: #gssa-calc(ms("E"), ms("T")))$,
  ["The CFG $L$ (with branches in #gssa-calc()) maps inputs $cal(K)$ to output $ms("L")$"],
  $klbrs(cal(K), L, A, annot: #reg-calc(ms("E"), ms("T")))$,
  ["The CFG $L$ (with branches in #reg-calc()) maps inputs $cal(K)$ to output $ms("L")$"],
  $ksbrs(cal(K), M, A, annot: #br-calc(ms("T"), ms("E")))$,
  ["The case-statement branches $M$ (in $#br-calc(ms("T"), ms("E"))$)
    map inputs $cal(K)$ to output $ms("L")$"],
)
and parametrized over judgements
#judgement-meaning(
  $hasty(Γ, e, A, annot: ms("E"))$,
  ["Expression $e ∈ ms("E")$ has type $A$ in $Γ$"],
  $haslb(Γ, τ, ms("L"), annot: ms("T"))$,
  ["Terminator $τ ∈ ms("T")$ takes context $Γ$ to cocontext $ms("L")$"],
  $isfn(Γ, f, A, B, annot: dfnl)$,
  ["$f ∈ dfnl$ takes inputs $A$ to outputs $B$ in $Γ$"],
  $hasty(Γ, α, A, annot: dael)$,
  ["Atomic expression $α ∈ dael$ has type $A$ in $Γ$"],
  $haslb(Γ, j, ms("L"), annot: ms("U"))$,
  ["Jump $j ∈ ms("U")$ takes context $Γ$ to cocontext $ms("L")$"],
)

We also introduced _metatheoretic_ judgements
#judgement-meaning(
  $issubst(Γ, γ, Δ)$,
  ["$γ$ is a substitution taking context $Δ$ to context $Γ$"],
  $lbsubst(cal("L"), ℓ, ms("K"))$,
  ["$ℓ$ is a label-substitution taking polycontext $cal("L")$ to cocontext $ms("K")$"],
)
as well as the notion of _renaming_ and _label-renaming_.


#todo[We've actually _used_ unions and friends above. So... makes sense to actually define them...]

#todo[We should probably also actually _define_ labels and friends]

#todo[segue...]

So far, we've defined at least five different typing judgements; to recap:

#judgement-meaning(
  $hasty(Γ, e, A)$,
  ["Expression $e ∈ #iter-calc(dfnl, dael)$ has type $A$ in $Γ$"],
  $istup(Γ, E, lb("T"))$,
  ["The fields $(E)$ have product type $Π lb("T")$ in $Γ$"],
  $kebrs(cal(K), M, A)$,
  ["The case branches $M$ map inputs $cal(K)$ to output $A$"],
  $haslb(Γ, r, ms("L"))$,
  ["Region $r ∈ #ssa-calc(ms("E"))$ takes context $Γ$ to cocontext $ms("L")$"],
)

dependent on user-provided judgements

#judgement-meaning(
  $isfn(Γ, f, A, B, annot: dfnl)$,
  ["$f ∈ dfnl$ takes inputs $A$ to outputs $B$ in $Γ$"],
  $hasty(Γ, α, A, annot: dael)$,
  ["Atomic expression $α ∈ dael$ has type $A$ in $Γ$"],
  $haslb(Γ, τ, ms("L"), annot: ms("T"))$,
  ["Terminator $τ ∈ ms("T")$ takes context $Γ$ to cocontext $ms("L")$"],
)

Naïvely, this means that we need to re-state properties like _weakening_ and _substitution_
for each such relation, leading to a combinatorial explosion.

Instead, we attempt to deal with this by introducing a uniform framework for dealing with
_typing relations_, based on the following core definition:

#definition(name: "Typing Relation")[
  Given cartesian typing disciplines $ms("X")$, $ms("Y")$, a _typing relation_

  $ms("W") : ms("X") sfn ms("Y")$ consists of:
  - A set of _terms_ $t ∈ |ms("W")|$
    -- where doing so is unambiguous, we identify $ms("W")$ with its set of terms
  - A typing relation $hasty(X, t, Y, annot: ms("W"))$
    where $X ∈ ms("X")$ and $Y ∈ ms("Y")$
  which is _stable under weakening_:
  - Given $hasty(X, t, Y, annot: ms("W"))$, for all $X' ⊑ X$ and $Y ⊑ Y'$,
    we have $hasty(X', t, Y', annot: ms("W"))$

  When the desired typing relation is clear from context, we drop the annotation,
  writing $hasty(X, t, Y)$ for $hasty(X, t, Y, annot: ms("W"))$.

  We write the set of typing relations with terms $|ms("W")| = W$ as $ms("X") stfn(W) ms("Y")$.
]

Probably the simplest example of a typing relation is the (unique) _empty relation_
$mb(0) = ms("X") sfn ms("Y")$ with no terms $|mb(0)| = ∅$.

We also define:

- The _union_ of typing relations $⋃_i ms("W")_i$, with
  - Terms $|⋃_i ms("W")_i| := ⋃_i |ms("W")_i|$
  - Typing relation $hasty(X, t, Y, annot: ⋃_i ms("W")_i) := ∃ i. hasty(X, t, Y, annot: ms("W")_i)$

- The _intersection_ of typing relations $⋂_i ms("W")_i$, with
  - Terms $|⋂_i ms("W")_i| := ⋂_i |ms("W")_i|$
  - Typing relation $hasty(X, t, Y, annot: ⋂_i ms("W")_i) := ∀ i. hasty(X, t, Y, annot: ms("W")_i)$

- A preorder on typing relations $ms("W") ⊑ ms("W")'$, which holds if and only if
  - For all $t ∈ |ms("W")|$, $X ∈ ms("X")$, and $Y ∈ ms("Y")$,
    if $hasty(X, t, Y, annot: ms("W"))$ then $hasty(X, t, Y, annot: ms("W")')$.

  This gives the set of typing relations the structure of a _complete prelattice_.

In general, for $W ⊆ W'$,
we implicitly coerce $ms("W") : ms("X") stfn(W) ms("Y")$
to $ms("W") : ms("X") stfn(W') ms("Y")$;
hence in particular:
- We have $mb(0) : ms("X") stfn(W) ms("Y")$ for all $W$.
- Unions and intersections lift to $ms("X") stfn(W) ms("Y")$
- Giving $ms("X") stfn(W) ms("Y")$ the structure of a _complete lattice_

While typing relations automatically respect weakening (and hence _subtyping_)
a good type system for expressions should not depend on the names of variables used
-- i.e., it should be _stable under renaming_.

For example, if $ms("X") := sctx(sty(ms("D")))$...

#todo[Context example]

#todo[Action-under-renaming...]

#todo[What do we call stable relations?]

#todo[expression relation...]

#definition(name: "Expression Signature")[
  An _expression signature_ $ms("E")$ over a cartesian typing discipline $ms("X")$
  is a typing relation $ms("E") : sctx(ms("X")) sfn ms("X")$ -- i.e.
  - A set of _terms_ $t ∈ |ms("E")|$
  - A typing relation $hasty(Γ, e, A, annot: ms("E"))$
    where $Γ ∈ sctx(ms("X"))$ and $A ∈ ms("X")$
    which is _stable under weakening_.
]

To deal with _functions_, however, we need to define weakening for arrows $A -> B$:
we do so by,
given a cartesian typing discipline $ms("X")$,
introducing the typing discipline of _arrows_
$adisc(ms("X"))$ with
- Types $A → B$ for $A, B ∈ ms("X")$
- Weakening $(A -> B) ⊑ (A' -> B') := (A' ⊑ A) ∧ (B ⊑ B')$

We may now define a closure signature as follows:

#todo["Closure signature" or "closure type relation"]

#definition(name: "Closure Signature")[
  A _closure signature_ $dfnl$ over a cartesian typing discipline $ms("X")$ is
  defined to be an expression signature over $adisc(ms("X"))$ -- i.e.
  - A set of _closures_ or _functions_ $f ∈ |dfnl|$
  - A typing relation $isfn(Γ, f, A, B, annot: dfnl)$
    where $Γ ∈ sctx(ms("X"))$ and $A, B ∈ ms("X")$
  which is _stable under weakening_:
  - Given $isfn(Γ, f, A, B, annot: dfnl)$,
    for all $Γ' ⊑ Γ$, $A' ⊑ A$, and $B ⊑ B'$,
    we have $isfn(Γ', f, A', B', annot: dfnl)$
]

#todo["Instruction signature" or "instruction type relation"]

#definition(name: "Instruction Signature")[
  An _instruction signature_ $dof$ over a typing discipline $ms("X")$ consists of:
  - A closure signature $dfnl$ over $ms("X")$; for typing _functions_
  - An expression signature $dael$ over $ms("X")$; for typing _atomic expressions_
]

#lemma[
  If $dof$ is an instruction signature over $sty(ms("X"))$,
  where $ms("X")$ is a cartesian typing discipline,
  then #dic is an expression signature over $sty(ms("X"))$
  with rules for $hasty(Γ, e, A, annot: #dic)$
  given in @cart-iter-calc-rules.
]

A good type system for expressions should not depend on the names of variables used
-- i.e., it should be _stable under renaming_.

In particular, given a _renaming_ $ρ : vrens$
-- i.e., a finitely supported injection from variables to variables, where
$
  fsup(ρ) := { x ∈ vset | ρ(x) ≠ x }
$
#todo[grammar]

These form a monoid under composition, with the identity $id$ as unit.

#todo[Make sure renamings are the right way around]

The monoid of renamings acts on contexts $Γ ∈ sctx(ms("X"))$ by pointwise application:
#eqn-set(
  $ρ · (·^⊗) := (·^⊗)$,
  $ρ · (Γ, x : A) := (ρ · Γ), (ρ(x) : A)$,
)
Writing $issubst(Γ, ρ, Δ) := cwk(ρ · Γ, Δ)$, we say that:

- We say an expression signature $ms("E")$ is _stable under renaming_ if:
  - It is equipped with a monoid action $ρ · e$ of renamings $ρ$ on expressions $e ∈ ms("E")$
    such that
  - Given a renaming $issubst(Γ, ρ, Δ)$,
    $hasty(Δ, e, A, annot: ms("E"))$ implies
    $hasty(Γ, ρ · e, A, annot: ms("E"))$
- Given an instruction signature $dof$
  - We define a _monoid action_ of renamings on $dof$ to consist of
    an monoid action on its closure signature and a monoid action on its expression signature
  - We say an instruction signature
    is _stable under renaming_ if both
    its closure signature and atomic expression signature are stable under renaming.

#todo[
  Pull up to right after expression definition -- then statement that #dic
  is an expression signature _includes_ both weakening and renaming.
]

Given a monoid action of renamings on an instruction signature $dof$,
we may define a monoid action of renamings on #dic by structural recursion,
with action on variables given by $ρ · x := ρ(x)$.

Note in particular that, by $α$-equivalence, we may avoid variable capture by
renaming bound variables to fresh names not appearing in the support of $ρ$.

#lemma(name: "Renaming")[
  If $dof$ is an instruction signature over a cartesian typing discipline $sty(ms("X"))$
  that is stable under renaming, then so is #dic.
]

In general, we will assume expression signatures,
and hence instruction signatures,
are stable under renaming and weakening by default.
To emphasize this,
we will call expression signatures where this is _not_ the case _raw_ signatures.

While we allow atomic expressions and closures to capture variables in general,
we can use renamings to single out the special case where they are in fact constant:

#definition(name: "Constant Signature")[
  An expression signature $dael$ over a cartesian typing discipline $ms("X")$
  is _constant_ if:
  - For all renamings $ρ$, $∀ α ∈ dael . ρ · α = α$
  - For all contexts $Γ$, $hasty(Γ, α, A) <==> hasty(·, α, A)$

  In particular, we call a constant closure signature a _function signature_.
]

We would now like to generalize renaming to _substitution_,
in which we replace variables $x$ with _arbitrary_ expressions $e$.

In particular, we'd like to recover the "usual" notion of substitution:

- A _substitution_ is a finitely supported function $γ : vset → #dic$,
  where we define the _support_ of a substitution to be given by
  $
    fsup(γ) := { x ∈ vset | γ(x) ≠ x }
  $

  We write the set of such substitutions as $substs(#dic)$.

- We _apply_ a substitution $γ ∈ substs(#dic)$
  to an expression $e ∈ #dic$;
  written $γ · e$;
  by recursively replacing each variable $x$ in $e$ with $γ(x)$
  -- in particular, as for renamings,
  $α$-renaming allows us to choose fresh variable names for all bound variables
  to avoid variable capture.

- If $issubst(Γ, γ, Δ)$, defined as, for all $cwk(Δ, x : A)$, $hasty(Γ, γ(x), A)$,
  then $hasty(Δ, e, A)$ implies $hasty(Γ, γ · e, A)$.

  In this case, we say that the expression signature #dic
  is _stable under substitution_.

One minor complication of this approach is that we need to define
what it means to substitute functions $f ∈ dfnl$ and atomic expressions $α ∈ dael$
-- that is,
to specify an _action_ of the set of substitutions $substs(#dic)$
on $dfnl$ and $dael$.

It turns out we can fit this into a general framework, along with renaming, as follows:

#definition(name: "Substitution Signature")[
  A _substitution signature_ $ms("S")$
  over a cartesian typing discipline $ms("X")$
  consists of a signature $ms("S") : sctx(ms("X")) sfn sctx(ms("X"))$ equipped with

  - An action of renamings on substitutions $γ ∈ |ms("S")|$

  - A partial function from renamings $ρ$ to substitutions $ren2subst(ρ) ∈ |ms("S")|$

  such that:

  - Whenever $ren2subst(ρ)$ is defined, $ρ' · ren2subst(ρ) = ren2subst(ρ' · ρ)$ is defined.

  - If $issubst(Γ, ρ, Δ)$ and $ren2subst(ρ)$ is defined, then $issubst(Γ, ren2subst(ρ), Δ)$, and

  - For all renamings $issubst(Γ', ρ, Γ)$, $issubst(Γ, γ, Δ)$ implies $issubst(Γ', ρ · γ, Δ)$

  We define an _action_ of a substitution signature $ms("S")$ on a set $L$
  to be a mapping from substitutions $γ ∈ ms("S")$ and terms $t ∈ L$
  to their _substitutions_ $γ · t ∈ L$.

  When unambiguous, we drop the explicit coercion and simply write $ρ$ for $ren2subst(ρ)$.

  We say that:
  - An expression signature $ms("E")$ is _stable under $ms("S")$_ if
    - It is equipped with an action of $ms("S")$ on expressions $e ∈ ms("E")$
    - Given a substitution $issubst(Γ, γ, Δ)$,
      $hasty(Δ, e, A, annot: ms("E"))$ implies
      $hasty(Γ, γ · e, A, annot: ms("E"))$
    - Whenever $ren2subst(ρ)$ is defined, we have $ren2subst(ρ) · e = ρ · e$
    - If $ms("E")$ is in fact constant, then the action of $ms("S")$ is trivial:
      $γ · e = e$ for all $γ ∈ ms("S")$ and $e ∈ ms("E")$
  - An instruction signature $dof$ is _stable under $ms("S")$_ if both
    its closure signature and atomic expression signature are stable under $ms("S")$.
]

Immediately, renaming emerges as a base case: $vrens$ is a substitution signature over
_every_ cartesian typing discipline $ms("X")$, with coercion $ren2subst(ρ) := ρ$
simply the identity.

#figure(
  [
    \
    #rule-set(
      declare-rule(r-iter-subst-nil),
      declare-rule(r-iter-subst-cons),
    )
    \
  ],
  caption: [
    Rules for typing substitutions $γ ∈ substs(ms("E"))$
    in a cartesian typing discipline $ms("X")$.
  ],
) <cart-subst-rules>

Similarly, given an expression signature $ms("E")$ over $ms("X")$
such that $ms("Var") ⊆ ms("E")$,
we may define a substitution signature $substs(ms("E"))$ with
- Terms $γ ∈ |substs(ms("E"))|$ given by finitely supported functions
  $vset → ms("E")$
- Typing relation $issubst(Γ, γ, Δ)$ given by the rules in @cart-subst-rules
- Coercions $ren2subst(ρ) ∈ |substs(ms("E"))|$ given by $ren2subst(ρ)(x) := ι(ρ(x))$
- Renaming action $(ρ · γ)(x) = ρ · γ(x)$

We may now state the _syntactic substitution lemma_ for $substs(#dic)$ as follows:

#lemma(name: "Substitution")[
  If $dof$ is stable under $substs(#dic)$, then so is #dic

  #todo[Unfolding things, this becomes (ye olde usual statement)]
]

= Refinement

#todo[
  - We want to study refinement and equivalence (state relation _between_ refinement and equivalence)
  - _To_ give rules for this, we need to track the effect of programs
  - So let's start with that!
]

#definition(name: "Typed relation")[
  Given a signature $ms("S") : ms("X") sfn ms("Y")$, we want to define a
  - _typed predicate_ on $ms("S")$ is a signature
    $ms("P") : ms("X") stfn(|ms("S")|) ms("Y")$ sat. congruence with $ms("P") ⊆ ms("S")$
  - _typed relation_ on $ms("S")$ is a signature
    $ms("R") : ms("X") stfn(|ms("S")| × |ms("S")|) ms("Y")$
    sat. congruence s.t. $ms("R") ⊆ ms("S") × ms("S")$
]

#let r-congr-var = rule(
  name: "var",
  $Γ ⊑ x : A$,
  $hasty(Γ, x, A, annot: "P")$,
);
#let r-congr-coe = rule(
  name: "coe",
  $hasty(Γ, a, A, annot: "P")$,
  $tywk(A, A')$,
  $hasty(Γ, a, A', annot: "P")$,
);
#let r-congr-atom = rule(
  name: "atom",
  $hasty(Γ, α, A, annot: ms("P")_dael)$,
  $hasty(Γ, α, A, annot: "P")$,
);
#let r-congr-app = rule(
  name: "app",
  $isfn(Γ, f, A, B, annot: ms("P")_dfnl)$,
  $hasty(Γ, a, A, annot: ms("P"))$,
  $hasty(Γ, f med a, B, annot: ms("P"))$,
);

#let fig-r-hasty = figure(
  [
    \
    #rule-set(
      declare-rule(r-congr-var),
      declare-rule(r-congr-coe),
      declare-rule(r-congr-atom),
      declare-rule(r-congr-app),
    )
    #todo[rest]
    \
  ],
  caption: [
    Congruence rules for a predicate
    #todo[this]
  ],
)

#fig-r-hasty <cart-iter-congr>

#let r-congr2-var = rule(
  name: "var",
  $Γ ⊑ x : A$,
  $hasty(Γ, (x, x), A, annot: "R")$,
);
#let r-congr2-coe = rule(
  name: "coe",
  $hasty(Γ, (a, a'), A, annot: "R")$,
  $tywk(A, A')$,
  $hasty(Γ, (a, a'), A', annot: "R")$,
);
#let r-congr2-atom = rule(
  name: "atom",
  $hasty(Γ, (α, α'), A, annot: ms("R")_dael)$,
  $hasty(Γ, (α, α'), A, annot: "R")$,
);
#let r-congr2-app = rule(
  name: "app",
  $isfn(Γ, (f, f'), A, B, annot: ms("R")_dfnl)$,
  $hasty(Γ, (a, a'), A, annot: ms("R"))$,
  $hasty(Γ, (f med a, f' med a'), B, annot: ms("R"))$,
);

#let fig-r-hasty = figure(
  [
    \
    #rule-set(
      declare-rule(r-congr2-var),
      declare-rule(r-congr2-coe),
      declare-rule(r-congr2-atom),
      declare-rule(r-congr2-app),
    )
    #todo[rest]
    \
  ],
  caption: [
    Congruence rules for a relation
    #todo[this]
  ],
)

#fig-r-hasty <cart-iter-congr2>

#definition(name: "Refinement basis")[
  A _refinement basis_ $ms("B")$ over $#dic$ consists of:
  - A monotone $cal(E)$-family of typed predicates $ms("B")(ε)$ ("has effect $ε$") with $ms("B")(⊤) = #dic$
  - A typed relation, _refinement_, $ms("B")_2$ on $#dic$
]

#definition(name: "Refinement System")[
  A _refinement system_ $ms("R")$ is a refinement basis $ms("B")$ closed under the rules
  in Figure ... + congruence
]

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

  Parametrized by (we assume $dfnl$ and $dael$ carry these as data...):
]

#judgement-meaning(
  $ehasty(Γ, dael, ε, α, A)$,
  ["The atomic expression $α$ has effect $ε$ in context $Γ$ at type $A$ in theory $dael$"],
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
