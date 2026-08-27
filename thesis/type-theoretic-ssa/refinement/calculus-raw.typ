// Mechanical transcription from:
// papers/isotope/complete-refinement-ssa.tex
// Repository commit: 9480278f2503902f0fa632d05d7f0c8faae893f3
// Sections: Introduction; SSA; lambda_iter syntax, typing, metatheory, and refinement
// Source lines: 277--295 and 326--1652
// Conversion: prose preserved verbatim; LaTeX presentation translated mechanically to Typst.

#import "/lib/prelude.typ": *
#import "/lib/figures/refinement-factorial.typ": refinement-factorial-figure

= Abstract

In this paper, we give a type-theoretic presentation of static single assignment (SSA) form, the
dominant compiler intermediate representation. Our type theory is very rich one, with
substructural types and an effect system, which enables us to give a syntactic presentation of
refinement for SSA programs which validates the effect-dependent program transformations that
compilers depend upon. We are also able to give a categorical semantics for our calculus, and we
prove our calculus both sound and complete with respect to the categorical axiomatization.
Completeness ensures that there are no missing refinements from our calculus, which lets compiler
writers validate optimizations in a model-free way. On the other side, the fact that our
axiomatization is sound gives us a syntax-free way of verifying that complex combinations of
features such as undefined behaviour, nondeterminism, and weak memory still validate the program
transformations compilers rely upon.

= Introduction
<refall:introduction>
Static single assignment form, or SSA, rapidly became the dominant
compiler intermediate representation (IR) after its introduction by
#cite(<alpern-ssa-original-88>, form: "prose") and
#cite(<rosen-gvn-1988>, form: "prose") in the 1980s. The fundamental
idea behind SSA is one which is very familiar to functional programmers:
if a variable is defined exactly once and never reassigned, then
substitution is then a valid program transformation. This both
simplifies the implementation and improves the performance of many
compiler optimizations.

The correctness of SSA transformations has mostly been handled
informally, because it was originally intended to be a simple,
first-order imperative programming language. Unfortunately, in the
decades since its introduction, computers have become much less simple,
and the optimizations that compiler writers want to do have become much
more complicated. Modern hardware is highly concurrent, and exhibits
user-visible non-sequentially-consistent behaviour: #emph[weak
memory];~#cite(<batty-compositional-17>). This means memory can no longer be
correctly modelled as a global array of bytes. Furthermore, compilers
like LLVM and GCC now perform very aggressive optimizations exploiting
knowledge of memory aliasing and undefined behaviour. Because all these
optimizations are all done in the presence of nondeterminism, the
transformations compilers want to do are not usually program
equivalences, but merely refinements: the possible behaviours of the
optimized program must be a subset of the possible behaviours of the
original program.

As a concrete example, consider the interaction of undefined behaviour
and other effects. The division operation
$sans(d i v) #h(0em) y #h(0em) z$ exhibits #emph[undefined behavior]
(UB) in both C and LLVM if $z$ is zero, but otherwise has no
side-effects. Therefore, the program
$sans(l e t) #h(0em) x = sans(d i v) #h(0em) y #h(0em) z ; #h(0em) e$ is
equivalent to $\[ sans(d i v) #h(0em) y #h(0em) z \/ x \] e$ if $z$ is
known to be nonzero, but not otherwise. For example, if $z = 0$ and
$e = \( \)$,
$sans(l e t) #h(0em) x = sans(d i v) #h(0em) y #h(0em) 0 ; #h(0em) \( \)$
always exhibits UB, whereas
$\[ sans(d i v) #h(0em) y #h(0em) 0 \/ x \] \( \) equiv \( \)$ simply
does nothing! However, one direction of the rewrite -- turning
$sans(l e t) #h(0em) x = sans(d i v) #h(0em) y #h(0em) z ; #h(0em) e$
into $\[ sans(d i v) #h(0em) y #h(0em) z \/ x \] e$ -- is always a safe
transformation, since:

- If $z$ is zero, then
  $sans(l e t) #h(0em) x = sans(d i v) #h(0em) y #h(0em) z ; #h(0em) e$
  has UB, so we can rewrite it to anything we want!

- Otherwise, $sans(d i v) #h(0em) y #h(0em) z$ is pure, so substitution
  is unconditionally valid

Note that this substitution moved a potentially-effectful operation
#emph[forward] in the program's execution. Depending upon how often $x$
occurs inside of $e$, this substitution could also duplicate or drop the
effectful operation. This observation gives rise to a categorization of
effectful terms, based on how they interact with substitution.

Because it is always safe to move UB after any other effect, we call it
a #emph[right-mover] with respect to that effect. Furtheremore, since it
is also always a refinement both to eliminate and to duplicate UB, we
say UB is both an #emph[eliminable] and #emph[duplicable] effect. This
is because eliminating UB reduces the set of possible behaviours, and
duplicating occurences of UB does not increase the set of possible
behaviours. We also have that
$\( sans(d i v) #h(0em) y #h(0em) z \, sans(d i v) #h(0em) y #h(0em) z \) arrow.r.twohead sans(l e t) #h(0em) x = sans(d i v) #h(0em) y #h(0em) z ; #h(0em) \( x \, x \)$,
so UB is also #emph[fusable]. When an effect is both fusable and
duplicable, we also call it #emph[relevant]. On the other hand, it is
not a refinement to introduce UB, since
$\( \) ↠̸ sans(l e t) #h(0em) x = sans(d i v) #h(0em) y #h(0em) z ; #h(0em) \( \)$.
Hence we say it is not #emph[introducible]. We say an effect which is
both #emph[eliminable] and #emph[introducible] is #emph[affine].

We might also want to ask with respect to which effects UB is a
#emph[left-mover], i.e., for which effects of $e$ we have
$\( e \, sans(d i v) #h(0em) y #h(0em) z \) arrow.r.twohead sans(l e t) #h(0em) x = sans(d i v) #h(0em) y #h(0em) z ; #h(0em) \( e \, x \)$
(with pairs evaluated left-to-right). With some thought, we can see this
refinement holds only when execution is guaranteed to continue after
evaluating $e$, so this rules out effects like nontermination or
exceptions, but effects like nondeterminism or memory access are fine.
That is, UB is a #emph[left-mover] with respect to nondeterminism and
memory access, but not in general. Since it is both a left and right
mover w.r.t. these effects, we say UB #emph[commutes] with them. An
effect that commutes with everything, like the empty effect $tack.t$, is
called #emph[central].

The question of what rewrites are permitted in the presence of effects
is one that compiler writers struggle with~#cite(<llvm-github>), because the
less conservative they are, the faster the code they can generate, but
the more dependent the are on having a clear understanding of each
effectful operation's semantics and interactions.

Because of this complexity, the old informal techniques are no longer
sufficient, and we need to study SSA using more mathematically
sophisticated techniques to understand and justify what modern hardware
and compilers do. In this paper, we introduce a type-theoretic account
of static single assigment form, and equip it with a semantics which
explains and can be used to justify many program transformations even in
the presence of effects like state, undefined behaviour, and weak memory
concurrency. Concretely, our contributions are as follows:

- First, we give a pair of type theories for SSA. The first language,
  $lambda_(sans(S S A))$, is intended to mimic the structure of
  traditional presentations of SSA. The second type theory,
  $lambda_(sans(i t e r))$, has a syntax very different from ordinary
  SSA, but which greatly facilitates giving a syntactic presentation of
  its refinement theory. Both of these theories have a rich type system
  with both linearity and effect tracking. The extra structure enables
  us to express many effect-dependent program transformations in a
  type-directed way. We show that $lambda_(sans(i t e r))$can be seen as
  an alternative presentation of ordinary SSA by showing that there are
  meaning-preserving translations to and from $lambda_(sans(S S A))$.

- We then give a categorical axiomatization of first-order effectful
  programs with looping and control, and then show that
  $lambda_(sans(i t e r))$is soundly interpreted in this model, and
  furthermore we show completeness of our refinement theory by proving
  that the syntactic model is the initial model.

- We then give a collection of concrete models validating the
  categorical axiomatization. We start with a model including
  nontermination, nondeterminism, and undefined behaviour, and then show
  how to give another model augmented with state, as well as giving a
  model for release-acquire concurrency which validates our axioms.
  Finally, we show how a variety of interesting optimizations are
  validated by our model.

Finally, many of the results in this paper have been mechanized in the
Lean proof assistant.

= SSA
<refall:sec:ssa-intro>
One of the first IRs to find widespread use was #emph[register transfer
level (RTL)] code. RTL programs are composed of a collection of
#emph[basic blocks], defined to be a sequence of instructions of the
form $x = f \( y \, z \)$ ending with a #emph[terminator] instruction,
which may branch to other basic blocks. The basic blocks, and the jumps
between them, form the nodes and edges of that program's
#emph[control-flow graph]. Because RTL variables are #emph[mutable],
program analyses have to keep track of the values of every variable
#emph[at every program point], significantly complicating performant
implementations.

To avoid this multplicative overhead, the #emph[static single
assignment], or #emph[SSA], IR enforces the restriction that every
variable has precisely one definition. Just as in functional programs,
this raises the question of how to handle control-flow dependent
variables such as loop induction variables. The answer is the same
#cite(<appel-ssa>): each basic block (or tail-recursive function!) takes a list
of control-flow dependent variables as #emph[arguments]. Traditionally,
these arguments are represented “inside out\" using
#emph[$phi.alt$-functions], which are assignments whose value depends
on which basic block is their immediate predecessor. Our formalization
follows modern practice and uses the #emph[basic blocks with arguments]
(BBA) representation of SSA.

In SSA, the property that every variable has a single definition is
graph-theoretic: we require that the use point of the variable is
#emph[dominated] by its definition in the control-flow graph.#footnote[A
node $n$ is dominated by a node $N$ in a directed graph if every path to
$n$ passes through $N$.] Semantics, however, is much easier with lexical
scoping. To interconvert between the two, we note that the dominance
relation on basic blocks always forms a tree rooted at the entry block:
we call this the #emph[dominator tree]. We will call a subtree of the
dominator tree, which has a single entry point (the root) and multiple
exits (the leaves, all dominated by the root), a #emph[region]. The
variables defined in a given basic block $beta$ are visible from another
block $beta'$ if and only if $beta$ dominates $beta'$, i.e., if $beta$
is a child in the dominator tree, contained in the region $r$ rooted at
$beta$. Hence, dominance based scoping can be represented as lexical
scoping #emph[with respect to the dominator tree].

This idea underlies the design of $lambda_(sans(S S A))$, what we call
#emph[type-theoretic SSA], which has the grammar given in
Figure~@refall:fig:ssa-syntax. Rather than give a grammar for basic-blocks and
control-flow graphs, we instead give a grammar for #emph[regions]
$r \, s \, t$, which are composed of a series of $sans(l e t)$-bindings
(each corresponding to an instruction $o$), followed by a subtree
$kappa$, which is composed of a terminator $tau$ wrapped in
$sans(w h e r e)$-blocks containing the region's dominated
subregions.#footnote[We distinguish recursive and non-recursive
$sans(w h e r e)$-blocks for effect-system bookkeeping, but semantically
they are identical.]

If we squint, we can see that this is just SSA with
$sans(w h e r e)$-blocks as an annotation representing the dominator
tree: basic blocks correspond to sequences of $sans(l e t)$-bindings
followed by a terminator. Indeed, it is straightforward to verify that
any well-scoped SSA program can be converted to a $lambda_(sans(S S A))$
program by simply adding in $sans(w h e r e)$-blocks corresponding to
the dominator tree; similarly, simply erasing the
$sans(w h e r e)$-blocks from an $lambda_(sans(S S A))$ program yields a
program in standard basic-blocks with arguments SSA; we see an example
of this in Figure~@refall:fig:fact-lex. We can also show that any two programs
which are equivalent up to the placement of $sans(w h e r e)$-blocks
have equivalent semantics, therefore justifying $lambda_(sans(S S A))$
as being simply SSA with additional annotations.

#refinement-factorial-figure()

#figure([#block[
  \<$o$\> ::= $x$ | $f #h(0em) x$ | $\( \)$ | $\( x \, y \)$ |
  $iota_l #h(0em) x$ | $iota_r #h(0em) x$ | $sans(a b o r t) #h(0em) x$

  \<$r \, s \, t$\> ::= $kappa$ | $sans(l e t) #h(0em) x = o ; t$ |
  $sans(l e t) #h(0em) \( x \, y \) = o ; t$

  \<$kappa$\> ::= $tau$ |
  $kappa #h(0em) sans(w h e r e)_(sans(n o n r e c)) #h(0em) L$ |
  $kappa #h(0em) sans(w h e r e)_(sans(r e c)) #h(0em) L$

  \<$tau$\> ::= $sans(b r) #h(0em) ell #h(0em) o$ |
  $sans(c a s e) #h(0em) o #h(0em) { iota_l #h(0em) y : tau \, iota_r #h(0em) z : tau' }$

  \<$L$\> ::= $dot.op$ | $L \, ell \( x \) : { t }$

  ]],
  caption: [
    Grammar for $lambda_(sans(S S A))$ programs.
  ]
)
<refall:fig:ssa-syntax>

#figure([```c++
  struct BasicBlock {
        vector<refall:Instruction> instructions;             // unary/binary let-bindings
        Terminator terminator;                        // LHS of where-block
        map<Label, (Argument, BasicBlock)> children;  // RHS of where-block
      }
  ```

  ],
  caption: [
    Data encoded by the grammar in Figure @refall:fig:ssa-syntax
  ]
)
<refall:fig:ssa-data>

= $lambda_(sans(i t e r))$, an expression language for SSA
<refall:lambda_ensuremathmathsfiter-an-expression-language-for-ssa>
SSA is a useful IR because it enables complex, whole-procedure
transformation of code, but its block-statement-value hierarchy makes it
difficult to uniformly formulate the allowed transformations as an
(in)equational theory. If we unified all of these levels into a single
expression language, then formulating many transformations becomes much
simpler. For example, if loops were an expression, then
control-flow-graph transformations which duplicate or fuse loop bodies
are merely instances of substitution (and its dual,
CSE/let-introduction).

In this section, we introduce $lambda_(sans(i t e r))$, which is an
expression-oriented variant of SSA. Essentially, it is a simple
first-order expression language with support for binding/sequencing,
branching, and loops. $lambda_(sans(i t e r))$ looks very different from
traditional presentations of SSA, but we later prove in
Subsection~#todo[Cross-reference: `refall:ssec:interconversion`] that the two syntaxes are completely
equivalent to one another. The main novelty of $lambda_(sans(i t e r))$
is in its type system and equational theory. It has a rich substructural
type and effect system, which enables us to give a complete inequational
characterization of refinement of $lambda_(sans(i t e r))$ programs.
Since $lambda_(sans(i t e r))$ is equivalent to SSA, we get a complete
syntactic characterization of refinement for SSA programs.

== Syntax and Typing Rules
<refall:syntax-and-typing-rules>
As mentioned before, $lambda_(sans(i t e r))$ is a standard first-order
expression language with branching and iteration: a functional analogue
of #smallcaps[While]. Its grammar is in Figure~@refall:fig:expr-syntax, and is
parametrized by a set of #emph[base types] $X in cal(X)$ and a set of
#emph[instructions] $f in cal(I)$. To model multiple arguments and
control flow, our grammar of types $A \, B \, C$ includes all
#emph[tensor products] $A ⊗ B$ and #emph[coproducts] $A + B$
generated by base types $X$, along with a #emph[unit type]
$upright(bold(1))$ and an #emph[empty type] $upright(bold(0))$.
Mirroring this, expressions $a \, b \, c$ consist of

- #emph[Variables] $x \, y \, z$

- #emph[Applications] $f #h(0em) a$, consisting of instructions
  $f in cal(I)$ applied to an expression $a$

- #emph[Let-bindings] $sans(l e t) #h(0em) x = a ; #h(0em) b$ and
  #emph[destructuring let-bindings]
  $sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) b$. We write $a ; b$
  as syntactic sugar for $sans(l e t) #h(0em) dot.op = a ; #h(0em) b$
  (i.e., a let binding where the bound variable is not used in $b$).

- #emph[Case-expressions]
  $sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b }$,
  representing branching control-flow

- #emph[Iteration-expressions]
  $sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : b }$
  representing a variant of #emph[tail-controlled loop], which:

  - Evaluates an initial value $a : A$

  - Evaluates the loop body $b : B + A$ with $x = a$; if the loop
    evaluates to a value of type $B$, we return it, otherwise, we
    re-evaluate the loop with $x$ having the new value of type $A$

#figure([#block[
  \<$A \, B \, C$\> ::= $X$ | $A ⊗ B$ | $upright(bold(1))$ |
  $A + B$ | $upright(bold(0))$

  \<$a \, b \, c$\> ::= $x$ | $f #h(0em) a$ |
  $sans(l e t) #h(0em) x = a ; #h(0em) b$ | $\( \)$ | $\( a \, b \)$ |
  $sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) b$ $iota_l #h(0em) a$
  | $iota_r #h(0em) b$ |
  $sans(c a s e) #h(0em) a #h(0em) { iota_l #h(0em) x : b \, iota_r #h(0em) y : c }$
  | $sans(a b o r t) #h(0em) a$ |
  $sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : b }$

  \<$q$\> ::= $0$ | $1$ | $omega^(+)$ | $1^(?)$ | $omega$

  \<$Gamma$\> ::= $dot.op$ | $Gamma \, x : A$

  \<$upright(bold(q))$\> ::= $dot.op$ | $upright(bold(q)) \, q$

  ]],
  caption: [
    Syntax for $lambda_(sans(i t e r))$ types, expressions, quantities,
    and contexts.
  ]
)
<refall:fig:expr-syntax>

Our typing judgement is
$Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A$. This says that in
the context $Gamma$, the expression $a$ has type $A$ and #emph[effects]
$epsilon.alt$, and uses $Gamma$'s variables according to the quantities
in the #emph[quantity vector] $upright(bold(q))$.

=== Variable Quantities
<refall:variable-quantities>
Our type system tracks how often individual variables are used to reason
about rewrites involving effectful expressions. Inspired by
substructural logic, which distinguishes linear (exactly once), affine
(at most once), and relevant (at least once), we introduce a join
semilattice of #emph[quantities] to model these usages. The primitive
quantities are:

- $0$ -- corresponding to being used zero times

- $1$ -- corresponding to being used exactly once

- $omega^(+)$ -- corresponding to being used multiple ($gt.eq 1$) times

This forms a partial order ${ 0 \, 1 lt.eq omega^(+) }$. To complete it
into a join-semilattice, we add elements

- $0 union.sq 1$ -- written $1^(?)$, corresponding to being used at most
  once

- $0 union.sq omega^(+)$ -- written $omega$, corresponding to being used
  any number of times

We call the set $Q^0 = { 0 \, 1 \, omega^(+) \, 1^(?) \, omega }$ the
#emph[extended] set of quantities, and
$Q = { 1 \, omega^(+) \, 1^(?) \, omega }$ the set of (#emph[nonzero])
quantities. $Q$ also forms a lattice, with $omega^(+) ∩ 1^(?) = 1$
(though $Q^0$ does not).

Contexts are a list $Gamma$ of typed variables $x : A$ along with a list
of quantities of equal length $upright(bold(q))$, which we write as
$Gamma^(upright(bold(q)))$. This is equivalent to annotating each
variable with a quantity $x : A^q$. We define the syntax sugars
$Gamma^(upright(bold(q))) \, x : A^q := \( Gamma \, x : A \)^(upright(bold(q)) \, q)$
and
$Gamma^(upright(bold(q))) \, x : A := \( Gamma \, x : A \)^(upright(bold(q)) \, omega)$.

Since we already track the usage of variables, it adds little extra
complexity to support substructural types (types whose elements can
#emph[only] be used a certain number of times). Assuming each base type
$X in cal(X)$ is equipped with a #emph[linearity]
$sans(q) \( X \) in Q$, the linearity of any type $A$ is defined as
$ sans(q) \( A ⊗ B \) = sans(q) \( A + B \) = sans(q) \( A \) ∩ sans(q) \( B \) #h(2em) sans(q) \( upright(bold(1)) \) = sans(q) \( upright(bold(0)) \) = omega $
We now define the linearity of annotated types $A^q$ and contexts
$Gamma$ as follows:
$ sans(q) \( dot.op \) = omega #h(2em) sans(q) \( Gamma^(upright(bold(q))) \, x : A^q \) = sans(q) \( Gamma^(upright(bold(q))) \) ∩ sans(q) \( A^q \) #h(2em) sans(q) \( A^q \) = cases(delim: "{", sans(q) \( A \) ∩ q & upright("if ") q eq.not 0, omega & upright("if ") q = 0) $
In particular, note that the linearity of an unused variable is always
unrestricted. We will enforce our quantity restrictions through the
means of #emph[weakening] and #emph[splitting] judgements, which will
determine how variables may be left unused or apportioned between
subcontexts, respectively. In particular, the judgement
$Gamma^(upright(bold(q))) mapsto Delta^(upright(bold(q))')$, pronounced
“$Gamma^(upright(bold(q)))$ weakens $Delta^(upright(bold(q')))$,\" is
defined as follows: #rule-set(
  prooftree(rule(label: msc("nil"), $dot.op mapsto dot.op$)),
  prooftree(rule(label: msc("cons"), $Gamma^(upright(bold(q))) mapsto Delta^(upright(bold(q))')$, $q' \* sans(q) \( A \) lt.eq q \* sans(q) \( A \)$, $Gamma^(upright(bold(q))) \, x : A^q mapsto Delta^(upright(bold(q))') \, x : A^(q')$)),
  prooftree(rule(label: msc("skip"), $Gamma^(upright(bold(q))) mapsto Delta^(upright(bold(q))')$, $0 lt.eq q \* sans(q) \( A \)$, $Gamma^(upright(bold(q))) \, x : A^q mapsto Delta^(upright(bold(q))')$)),
) To define weakening, we extend the meet on $Q$ to a
#emph[product] of quantities $q \, q' in Q^0$ as follows:
$ q \* q' = cases(delim: "{", 0 & upright("if ") q = 0 upright(" or ") q' = 0, q ∩ q' & upright("if ") q \, q' in Q) $
The rule skip says affine variables are discarable, which it encodes via
the condition $0 lt.eq q \* sans(q) \( A \)$. The rule cons says that we
may replace a variable quantity $q$ with another quantity $q'$ allowing
less permissive usage #emph[relative to the type's quantity]. For
example, for an affine type $A$ (usable $1^(?)$), the quantity
$omega^(+)$ forces linear usage ($omega^(+) \* 1^(?) = 1$), whereas the
quantity $1^(?)$ still permits deletion ($1^(?) \* 1^(?) = 1^(?)$). This
induces a #emph[preorder] on contexts, with two contexts equivalent if
their component variables can be used the same way. We now define
#emph[context splitting]
$Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$
as follows: #rule-set(
  prooftree(rule(label: msc("nil"), $dot.op tack.r dot.op = dot.op + dot.op$)),
  prooftree(rule(label: msc("both"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $omega^(+) lt.eq q ∩ sans(q) \( A \)$, $Gamma \, x : A tack.r \( upright(bold(q)) \, q \) = \( upright(bold(q))_l \, q \) + \( upright(bold(q))_r \, q \)$)),
  prooftree(rule(label: msc("left"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma \, x : A tack.r \( upright(bold(q)) \, q \) = \( upright(bold(q))_l \, q \) + \( upright(bold(q))_r \, 0 \)$)),
  prooftree(rule(label: msc("right"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma \, x : A tack.r \( upright(bold(q)) \, q \) = \( upright(bold(q))_l \, 0 \) + \( upright(bold(q))_r \, q \)$)),
) The rules left and right allow us to use a variable,
regardless of quantity, in either subexpression, whereas the rule both
states that it must be relevant to be used in both branches.

=== Effects
<refall:effects>
Our language of effects is a bounded#footnote[has a maximum element
$top$ and minimum element $tack.t$] join-semilattice $cal(E)$. We will
represent pure expressions as having the bottom effect $tack.t$, whereas
expressions with effect $top$ have "arbitrary" effect, and expressions
with effect $epsilon.alt union.sq epsilon.alt'$ have both effects
$epsilon.alt$ and $epsilon.alt'$.

Becaise we want to rewrite effectful programs it is not enough to know
which effects a program might have: we also need to know how they
interact. In particular, we need to know:

+ Which effects are #emph[iterable], i.e., stable under loops.

+ The #emph[multiplicity] of each effect $epsilon.alt$ : whether it is
  #emph[duplicable], #emph[fusable], #emph[introducible], or
  #emph[eliminable].

+ If effect $epsilon.alt$ is a #emph[left-mover] or #emph[right-mover]
  relative to $eta$ (i.e. can $epsilon.alt$ be moved before or after
  $eta$)

Not all effects are stable under arbitrary iteration. For example, a
pure, total computation iterated infinitely often can now exhibit the
effect of nontermination. Indeed, any total effect (such as reading or
writing from a location) repeated infinitely often can gain the
nontermination effect. To model stability, we are going to require that
there is an upwards-closed subset $cal(E)^oo subset.eq cal(E)$ of
#emph[iterative effects]. The intuition behinds the upwards-closed
requirement is that once nontermination is in the effect $epsilon.alt$,
then it will continue to be present in any supereffect.

To represent multiplicity, we take advantage of the fact that we already
have a notion of quantitity. Unlike in ordinary linear type systems, we
are interested in refinement (a directed notion) rather than pure
equations. We split the property of contraction into the pair of
properties #emph[duplicability] and #emph[fusability]: contraction in
each direction of refinement. Likewise weakening splits into the pair of
directed weakening properties of #emph[eliminability] and
#emph[introducability]. To model this, we assign a #emph[pair] of
quantities $sans(q)^(+) \( e \) \, sans(q)^(-) \( e \) in Q$ to each
effect, such that

- An effect can be eliminated if $1^(?) lt.eq sans(q)^(+) \( e \)$, and
  introduced if $1^(?) lt.eq sans(q)^(-) \( e \)$

- An effect can be duplicated if $omega^(+) lt.eq sans(q)^(+) \( e \)$,
  and fused if $omega^(+) lt.eq sans(q)^(-) \( e \)$

To be compatible with our notion of sub-effect, such a map should be
#emph[antitone] and have the property that
$sans(q)^p \( tack.t \) = omega$ for $p in { + \, - }$ (i.e., pure
computations can be used as often as you like).

Finally, we need to know how effects can be reordered. For example, a
memory read and an IO write cannot interfere, and hence can be
reordered. To model this, we introduce a #emph[directed commutativity
relation] $harpoon.rt subset.eq cal(E) times cal(E)$. If
$epsilon.alt harpoon.rt epsilon.alt'$, then a computation performing
$epsilon.alt$-effects can be moved past a computation performing
$epsilon.alt'$-effects without introducing new behaviour. We require
that $tack.t harpoon.rt epsilon.alt$ and
$epsilon.alt harpoon.rt tack.t$, to ensure that pure computations can be
moved freely, and we also require that the relation is antitone, to
model that decreasing the number of effects never loses rewrites. We
introduce the syntax sugar
$epsilon.alt harpoon.lb eta arrow.l.r.double eta harpoon.rt epsilon.alt$,
$epsilon.alt harpoons.rtlb eta arrow.l.r.double epsilon.alt harpoon.rt eta and epsilon.alt harpoon.lb eta$.
For polarities $p in { + \, - }$, we define $harpoon.rt^p$ in the
obvious manner, with
$epsilon.alt harpoon.rt^(+) eta arrow.l.r.double epsilon.alt harpoon.rt eta$
and
$epsilon.alt harpoon.rt^(-) eta arrow.l.r.double epsilon.alt harpoon.lb eta$.
Putting all this together, we may now define an #emph[effect system] as
follows:

#block[
An #emph[effect system] $cal(E)$ is a bounded join-semilattice $cal(E)$
equipped with:

- an upwards closed subset $cal(E)^oo$ of #emph[iterative effects]
  containing $top$, and

- a pair of antitone maps
  $sans(q)^(+) \, sans(q)^(-) : cal(E) arrow.r Q$ which map $tack.t$ to
  $omega$,

- a #emph[directed commutativity relation]
  $harpoon.rt subset.eq cal(E) times cal(E)$, an antitone relation
  containing $tack.t harpoon.rt epsilon.alt$ and
  $epsilon.alt harpoon.rt tack.t$ for all $epsilon.alt$.

]
=== Typing rules
<refall:typing-rules>
We now have all the pieces we need to define a
$lambda_(sans(i t e r))$-#emph[signature]:

#block[
A $lambda_(sans(i t e r))$signature
$cal(S) = \( cal(X) \, cal(I) \, cal(E) \)$ consists of a set of
#emph[base types] $X in cal(X)$, a set of #emph[instructions]
$f in cal(I)$, and an iterative effect system $cal(E)$ such that we
associate:

- Every base type $X$ type to a #emph[quantity]
  $sans(q) \( X \) in { 1 \, 1^(?) \, omega^(+) \, omega }$.

- Every instruction to a #emph[source type] $sans(s r c) \( f \) = A$, a
  #emph[target type] $sans(t r g) \( f \) = B$, and an #emph[effect]
  $sans(e f f) \( f \) = epsilon.alt$.

]
All the following definitions in this section will be with respect to an
arbitrary $lambda_(sans(i t e r))$-signature $cal(S)$. We give the
typing rules for $lambda_(sans(i t e r))$ in Figure~@refall:fig:expr-typing.
Our rules are syntax directed, with one rule for each production in our
grammar. In particular,

- The var rule says that a variable $x$ has type $A$ in the context
  $Gamma^(upright(bold(q)))$ if $Gamma^(upright(bold(q)))$ weakens to
  the singleton context $x : A^1$, i.e., if $x$ has nonzero quantity and
  all other (unused) variables are affine. Since accessing a variable is
  pure, we can give it an arbitrary effect $epsilon.alt$.

- To type a let-binding $sans(l e t) #h(0em) x = a ; #h(0em) e$ in
  $Gamma^(upright(bold(q)))$ with let$""_1$ with effect $epsilon.alt$,
  we must:

  - Split the context into a left-component $upright(bold(q))_l$ and a
    right-component $upright(bold(q))_r$, such that:

  - $a$ is well-typed and has effect $epsilon.alt$ in the #emph[right]
    component $Gamma^(upright(bold(q))_r)$, and $b$ is well-typed in
    $Gamma^(upright(bold(q))_l)$ plus an unrestricted parameter
    $x : A^top$.

- case and let$""_2$ are similar, except that let$""_2$'s body requires
  two parameters (one for each component of the tensor product), while
  both branches of a case-statement share the #emph[same] left-component
  $Gamma^(upright(bold(q))_l)$ (since exactly one branch is executed.)

- unit is well-typed and pure (and therefore can be assigned an
  arbitrary effect $epsilon.alt$) in any context composed solely of
  affine variables, i.e. satisfying
  $Gamma^(upright(bold(q))) mapsto dot.op$.

- pair splits the context between the left and right components and
  checks each one,

- The iter rule is the most complex: we split the context into a
  component $upright(bold(q))_r$ for the initial value and a component
  $upright(bold(q))_l$ for the body. The initial value is then evaluated
  and passed in as an additional parameter of type $A$ to the body.
  $upright(bold(q))_l$ must be unrestricted, since the loop may execute
  any number of times. Finally, the effect of the loop body must be an
  iterative effect.

#figure([#block[
#rule-set(
  prooftree(rule(label: msc("var"), $Gamma^(upright(bold(q))) mapsto x : A^1$, $Gamma^(upright(bold(q))) tack.r epsilon.alt x : A$)),
  prooftree(rule(label: msc("let1"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_l) \, x : A tack.r epsilon.alt b : B$, $Gamma^(upright(bold(q))) tack.r sans(l e t) #h(0em) x = a ; #h(0em) b : B$)),
  prooftree(rule(label: msc("op"), $f : A arrow.r_epsilon.alt B$, $Gamma^(upright(bold(q))) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))) tack.r epsilon.alt f #h(0em) a : B$)),
  prooftree(rule(label: msc("inst"), $f in cal(I)$, $sans(s r c) \( f \) = A$, $sans(t r g) \( f \) = B$, $sans(e f f) \( f \) lt.eq epsilon.alt$, $f : A arrow.r_epsilon.alt B$)),
  prooftree(rule(label: msc("unit"), $Gamma^(upright(bold(q))) mapsto dot.op$, $Gamma^(upright(bold(q))) tack.r epsilon.alt \( \) : upright(bold(1))$)),
  prooftree(rule(label: msc("pair"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_l) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt b : B$, $Gamma^(upright(bold(q))) tack.r epsilon.alt \( a \, b \) : A ⊗ B$)),
  prooftree(rule(label: msc("let2"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r a : A ⊗ B$, $Gamma^(upright(bold(q))_l) \, x : A \, y : B tack.r epsilon.alt c : C$, $Gamma^(upright(bold(q))) tack.r epsilon.alt sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) c : C$)),
  prooftree(rule(label: msc("inl"), $Gamma^(upright(bold(q))) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))) tack.r epsilon.alt iota_l #h(0em) a : A + B$)),
  prooftree(rule(label: msc("inr"), $Gamma^(upright(bold(q))) tack.r epsilon.alt b : B$, $Gamma^(upright(bold(q))) tack.r epsilon.alt iota_r #h(0em) b : A + B$)),
  prooftree(rule(label: msc("abort"), $Gamma^(upright(bold(q))) tack.r epsilon.alt a : upright(bold(0))$, $Gamma^(upright(bold(q))) tack.r epsilon.alt sans(a b o r t) #h(0em) a : C$)),
  prooftree(rule(label: msc("case"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt e : A + B$, $Gamma^(upright(bold(q))_l) \, x : A tack.r epsilon.alt a : C$, $Gamma^(upright(bold(q))_l) \, y : B tack.r epsilon.alt b : C$, $Gamma^(upright(bold(q))) tack.r epsilon.alt sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } : C$)),
  prooftree(rule(label: msc("iter"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $sans(q) \( Gamma^(upright(bold(q))_l) \) = omega$, $epsilon.alt in cal(E)^oo$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_l) \, x : A tack.r epsilon.alt b : B + A$, $Gamma^(upright(bold(q))) tack.r epsilon.alt sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : b } : B$)),
)

  ]],
  caption: [
    Typing rules for $lambda_(sans(i t e r))$
  ]
)
<refall:fig:expr-typing>

== Syntactic Metatheory
<refall:syntactic-metatheory>
As a basic sanity check, we can verify that our calculus admits
#emph[weakening]:

#block[
If $Gamma'^(upright(bold(q))') mapsto Gamma^(upright(bold(q)))$ and
$Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A$ then
$Gamma'^(upright(bold(q))') tack.r_epsilon.alt a : A$.

]
We now define substitution for effectful terms. First, we define a
judgement
$Gamma^(upright(bold(q))) tack.r_epsilon.alt sigma gt.tri Delta^(upright(bold(q))')$
for substitutions, with rules in Figure~@refall:fig:expr-subst. This may be
read as "$sigma$ takes the context $Gamma^(upright(bold(q)))$ to the
context $Delta^(upright(bold(q))')$ with effect $epsilon.alt$." Our
rules may be interpreted as follows:

- nil says that the empty substitution $dot.op$ takes any affine context
  $Gamma^(upright(bold(q)))$ to the empty context $dot.op$. This holds
  because a well-typed term in the empty context is also well-typed in
  any affine context. The effect is an arbitrary $epsilon.alt$, since
  the empty substitution is always pure.

- zero rule says that if a variable $x : A^0$ is unused, then we can map
  it to an arbitrary (even ill-typed) term $a$. Since $x$ will never
  appear in a well-typed term, $a$ will never appear in their
  substitutions, and therefore needs no restrictions. The effect
  $epsilon.alt$ of $sigma$ is unchanged.

- cons: to type a substitution $sigma \, x mapsto a$ taking
  $Gamma^(upright(bold(q)))$ to $Delta^(upright(bold(q))') \, x : A^q$
  with effect $epsilon.alt$, we split the input context into a context
  $Gamma^(upright(bold(q))_l)$, used to type $sigma$ with effect
  $epsilon.alt_l lt.eq epsilon.alt$, and $Gamma^(upright(bold(q))_r)$,
  used to type $a$ with effect $epsilon.alt_r lt.eq epsilon.alt$.
  $Gamma^(upright(bold(q))_r)$ must be useable with quantity $q$; i.e.,
  is relevant if $q$ is relevant and affine if $q$ is affine. Finally,
  the effect of $sigma$ ($epsilon.alt_l$) and the effect of $a$
  ($epsilon.alt_r$) must commute.

#figure([#block[
#rule-set(
  prooftree(rule(label: msc("nil"), $Gamma^(upright(bold(q))) mapsto dot.op$, $Gamma^(upright(bold(q))) tack.r epsilon.alt dot.op gt.tri dot.op$)),
  prooftree(rule(label: msc("zero"), $Gamma^(upright(bold(q))) tack.r epsilon.alt sigma gt.tri Delta$, $Gamma^(upright(bold(q))) tack.r epsilon.alt sigma \, x mapsto a gt.tri Delta^(upright(bold(q))') \, x : A^0$)),
  prooftree(rule(label: msc("cons"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q_l))) tack.r epsilon.alt_l sigma gt.tri Delta^(upright(bold(q)))$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt_r a : A$, $q lt.eq sans(q) \( Gamma^(upright(bold(q))_r) \)$, $epsilon.alt_l harpoons.rtlb epsilon.alt_r$, $epsilon.alt_l \, epsilon.alt_r lt.eq epsilon.alt$, $Gamma^(upright(bold(q))) tack.r epsilon.alt sigma \, x mapsto a gt.tri Delta^(upright(bold(q))') \, x : A^q$)),
)

  ]],
  caption: [
    Substitution rules for $lambda_(sans(i t e r))$
  ]
)
<refall:fig:expr-subst>

We write $\[ sigma \]$ for the action of substitution $sigma$ on term
$a$. We can now state substitution:

#block[
If
$Gamma'^(upright(bold(q))') tack.r_epsilon.alt sigma gt.tri Gamma^(upright(bold(q)))$
and $Gamma^(upright(bold(q))) tack.r_epsilon.alt a : A$ then
$Gamma'^(upright(bold(q))') tack.r_epsilon.alt \[ sigma \] a : A$.

]
== Refinement Theory
<refall:ssec:refinement-theory>
We now define our core notion of refinement. The judgment
$ Gamma^(upright(bold(q))) tack.r_(cal(R)) a arrow.r.twohead b : A $
means $a$ is refined by $b$ in the context $Gamma^(upright(bold(q)))$,
modulo rewrites $cal(R)$. Intuitively, this expresses that $b$ is at
least as defined or deterministic as $a$, possibly after applying known
rewrites in $cal(R)$. We define equivalence of terms as mutual
refinement:
$ Gamma^(upright(bold(q))) tack.r_(cal(R)) a approx b : A arrow.l.r.double Gamma^(upright(bold(q))) tack.r_(cal(R)) a arrow.r.twohead b : A and Gamma^(upright(bold(q))) tack.r_(cal(R)) b arrow.r.twohead a : A $
For notational convenience, we also use a polarity-marked notation for
refinement relation:
$ Gamma^(upright(bold(q))) tack.r_(cal(R)) a arrow.r.twohead^(+) b : A arrow.l.r.double Gamma^(upright(bold(q))) tack.r_(cal(R)) a arrow.r.twohead b : A #h(2em) Gamma^(upright(bold(q))) tack.r_(cal(R)) a arrow.r.twohead^(-) b : A arrow.l.r.double Gamma^(upright(bold(q))) tack.r_(cal(R)) b arrow.r.twohead a : A $

A #emph[rewrite system] $cal(R)$ consists of a set judgments of the form
$Gamma^(upright(bold(q))) tack.r_() a arrow.r.twohead b : A$ closed
under pure substitution. That is, given a pure substitution $sigma$, we
have that #rule-set(
  prooftree(rule(label: msc("rule"), $Gamma^(upright(bold(q))) tack.r tack.t sigma gt.tri Delta^(upright(bold(q))')$, $\( Delta^(upright(bold(q))') tack.r a arrow.r.twohead b : A \) in cal(R)$, $\( Gamma^(upright(bold(q))) tack.r \[ sigma \] a arrow.r.twohead \[ sigma \] b : A \) in cal(R)$)),
)
We will often describe a rewrite system as that #emph[generated] by a
set of equations with free variables; e.g., the system generated by
$x : bb(N) \, y : bb(N) tack.r_() sans(a d d) #h(0em) \( x \, y \) arrow.r.twohead sans(a d d) #h(0em) \( y \, x \) : bb(N)$.
Our goal is to construct a refinement relation $arrow.r.twohead$
satisfying the following properties:

+ #strong[Inclusion of $cal(R)$:] all given rewrites are valid
  refinements. <refall:item:includes-rewrites>

+ #strong[Congruence:] $arrow.r.twohead$ is closed under term formers
  and is a preorder. <refall:item:is-congruence>

+ #strong[Let-normalization:] $arrow.r.twohead$ abstracts away syntactic
  associativity of let-bindings. <refall:item:abstracts-syntax>

+ #strong[Universal properties:] $arrow.r.twohead$ validates the $beta$-
  and $eta$-laws of the language. <refall:item:does-computation>

+ #strong[Iteration semantics:] $arrow.r.twohead$ captures fixpoint and
  control-flow behavior of iteration. <refall:item:does-iteration>

We guarantree that $arrow.r.twohead$ contains the (reflexive, transitive
closure of) $cal(R)$, and therefore satisfies
property~#link(<refall:item:includes-rewrites>)[1], by the following rules:
#rule-set(
  prooftree(rule(label: msc("base"), $\( Gamma^(upright(bold(q))) tack.r a arrow.r.twohead b : A \) in cal(R)$, $Gamma^(upright(bold(q))) tack.r cal(R) a arrow.r.twohead b : A$)),
  prooftree(rule(label: msc("refl"), $Gamma^(upright(bold(q))) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))) tack.r cal(R) a arrow.r.twohead a : A$)),
  prooftree(rule(label: msc("trans"), $Gamma^(upright(bold(q))) tack.r cal(R) a arrow.r.twohead b : A$, $Gamma^(upright(bold(q))) tack.r cal(R) b arrow.r.twohead c : A$, $Gamma^(upright(bold(q))) tack.r cal(R) a arrow.r.twohead c : A$)),
) The other congruence rules (in the appendix in
Figure~#todo[Cross-reference: `refall:fig:congruence-refinement`]) correspond one-to-one with our term
formers to ensure property~#link(<refall:item:is-congruence>)[2].
Property~#link(<refall:item:is-congruence>)[2] means that the induced equivalence $approx$
is also a congruence.

To satisfy property~#link(<refall:item:abstracts-syntax>)[3], we introduce the binding
rules (Figure~@refall:fig:binding-rules), which are stated as equivalences.
These rules express syntactic equivalences up to reassociation and
let-floating. For instance, nested let-bindings are rearranged to a
canonical form. We do not require binding rules for every
construct---rules for pairs and sums, for example, can be derived via
$beta$-reduction.

Property~#link(<refall:item:does-computation>)[4] is addressed via the reduction rules
(Figure~@refall:fig:reduction-rules). Most of these are standard $beta$- and
$eta$-equivalences. However, the rule let$""_1$-$beta^p$ is
#emph[directional]: it expresses that
$sans(l e t) #h(0em) x = a ; #h(0em) b$ refines $\[ x \/ a \] b$ when
the effect $epsilon.alt$ of $a$ is a right-mover with respect to the
effect $eta$ of $b$, and when $x$ is used in a way compatible with
$epsilon.alt$ and the context. We also require that the context
$Gamma^(upright(bold(q))_r)$ used to type $a$ has a linearity compatible
with the usage of $x$ in $b$, as well as with the effect $epsilon.alt$
(for example, since printing is linear, if $a$ performs printing then
$x$ must be used linearly in $b$ even if $b$ is pure). The reverse
direction is permitted only under the dual (left-mover) condition. Thus,
the usual $beta$-equation:
$ Gamma^(upright(bold(q))) tack.r_(cal(R)) sans(l e t) #h(0em) x = a ; #h(0em) b approx \[ x \/ a \] b : B $
is derivable under sufficient purity assumptions, and in particular
always holds when $epsilon.alt = tack.t$. The rule elim, at first
glance, can be viewed as a special case of let$""_1$-$beta^p$ (combined
with term), but is introduced as a separate rule since it does
#emph[not] require $Gamma^(upright(bold(q))_l)$ to be affine to delete
$a$.

In particular, this means that the following more standard typing rule
is #emph[derivable]:
#rule-set(
  prooftree(rule(label: msc("let1-beta"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_l) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_r) \, x : A^q tack.r eta b : B$, $epsilon.alt harpoons.rtlb eta$, $q lt.eq sans(q) \( Gamma^(upright(bold(q))_r) \) ∩ sans(q) \( epsilon.alt \)$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) x = a ; #h(0em) b approx \[ x \/ a \] b : B$)),
) In particular, this obviously holds for pure expressions with
$epsilon.alt = tack.t$ (modulo linearity of
$Gamma^(upright(bold(q))_r)$), as we would normally expect in an
effectful language.

The last thing that remains is to treat iteration. Our rules for
iteration, given in Figure~@refall:fig:iteration-rules, are based on the
properties of a Conway iteration operator as given in
#cite(<coinductive-resumption-levy-goncharov-19>, form: "prose"). In
particular, we require our operator to satisfy the following properties:

==== Fixpoint
<refall:fixpoint>
behavior is encoded by the rule iter-$beta$, which expresses that
iteration behaves as a least fixpoint. That is,
$sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : b }$ evaluates to
$a$, then to $b \[ a \/ x \]$, and depending on the result of $b$,
either exits with a value in the left branch or continues recursively
with a value in the right branch. This unfolds the iteration into a case
split
$sans(l e t) #h(0em) x = a ; #h(0em) sans(c a s e) #h(0em) b #h(0em) { iota_l #h(0em) y : y \, iota_r #h(0em) z : sans(i t e r) #h(0em) z #h(0em) { iota_r #h(0em) x : b } }$
capturing precisely one unfolding of the loop. This gives rise to an
inductive account of iteration semantics that meshes naturally with
refinement.

==== Naturality,
<refall:naturality>
expressed by the rule let-iter, states that sequencing a computation $c$
after a loop can be interchanged with sequencing $c$ inside the loop's
exit branch. This enables reasoning about program structure independent
of surface syntax and supports loop-invariant motion of subsequent code.

==== Codiagonality,
<refall:codiagonality>
via the rule codiag, states that nested iterations of the same body can
be collapsed into a single iteration by fusing their recursive branches.
Operationally, this justifies flattening nested loops into one with a
more complex continuation.

==== Uniformity,
<refall:uniformity>
via the rule unif$""^p$, allows us to effectively commute certain
effectful operations with the infinite unrolling of a loop body. This is
best explained in terms of control-flow graphs: the precondition of the
rule is corresponds to the left-hand-side of the diagram in
Figure~@refall:fig:unif-cfg, while the postcondition corresponds to the
right-hand-side. If we unroll the loops on both sides "infinitely many
times," to obtain an infinite tree, we see that unif$""^p$ just says
that we can apply the rewrite on the left-hand-side "infinitely many
times" to convert a tree of $b$'s into a tree of $b'$'s. The name
uniformity is by analogy to uniformity in analysis, in which an
operation can be used to uniformly transmute each term of an infinite
series (rather than only be valid for a finite number of terms).

Note that we #emph[cannot] do this for an arbitrary $s$; we need it to
#emph[commute] with the effect of the loop. For example, if the effect
of the loop is (potential) nontermination, and $s$ contains a
print-statement, uniformity does #emph[not] apply, since while for any
given iteration of the loop body we have, where
$sans(p r i n t) : upright(bold(1))$ and
$sans(e x p r) : upright(bold(1)) + upright(bold(1))$ commutative with
printing (e.g., reading and writing from memory),
$sans(p r i n t) ; sans(e x p r) approx sans(c a s e) #h(0em) sans(e x p r) #h(0em) { iota_l #h(0em) x : iota_l #h(0em) sans(p r i n t) \, iota_r #h(0em) y : iota_l #h(0em) sans(p r i n t) }$
but
$ sans(i t e r) #h(0em) sans(p r i n t) #h(0em) { iota_r #h(0em) dot.op : sans(e x p r) } approx.not sans(i t e r) #h(0em) \( \) #h(0em) { iota_r #h(0em) dot.op : sans(c a s e) #h(0em) sans(e x p r) #h(0em) { iota_l #h(0em) x : iota_l #h(0em) sans(p r i n t) \, iota_r #h(0em) y : iota_l #h(0em) y } } $
since the latter may delay the print-statement infinitely far into the
future, and hence hang before printing. On the other hand, if we instead
have commutative effects (e.g., if $s$ has nondeterminism and the loop
has printing and nontermination), we can safely perform the infinite
rewrite.

We will denote the set of refinements generated by a set of base
refinements $cal(R)$ as $sans(T h) \( cal(R) \)$. In particular, we note
that $sans(T h) \( dot.op \)$ is monotonic, idempotent, and satisfies
$cal(R) subset.eq sans(T h) \( cal(R) \)$, making it a closure operator.

#figure([#block[
#rule-set(
  prooftree(rule(label: msc("let-op"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $f : A arrow.r_epsilon.alt B$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_l) \, y : B tack.r epsilon.alt c : C$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) y = f #h(0em) a ; #h(0em) c approx sans(l e t) #h(0em) x = a ; #h(0em) sans(l e t) #h(0em) y = f #h(0em) x ; #h(0em) c : C$)),
  prooftree(rule(label: msc("let-let1"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_c + upright(bold(q))_r$, $Gamma tack.r upright(bold(q))_c = upright(bold(q))_l + upright(bold(q))_m$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_m) \, x : A tack.r epsilon.alt b : B$, $Gamma^(upright(bold(q))_l) \, y : B tack.r epsilon.alt c : C$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) y = \( sans(l e t) #h(0em) x = a ; #h(0em) b \) ; #h(0em) c approx sans(l e t) #h(0em) x = a ; #h(0em) sans(l e t) #h(0em) y = b ; #h(0em) c : C$)),
  prooftree(rule(label: msc("let-let2"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_c + upright(bold(q))_r Gamma tack.r upright(bold(q))_c = upright(bold(q))_l + upright(bold(q))_m$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : A ⊗ B$, $Gamma^(upright(bold(q))_m) \, x : A \, y : B tack.r epsilon.alt c : C$, $Gamma^(upright(bold(q))_l) \, z : C tack.r epsilon.alt d : D$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) z = \( sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) c \) ; #h(0em) d approx sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) sans(l e t) #h(0em) z = c ; #h(0em) d : D$)),
  prooftree(rule(label: msc("let-case"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_c + upright(bold(q))_r Gamma tack.r upright(bold(q))_c = upright(bold(q))_l + upright(bold(q))_m$, $Gamma^(upright(bold(q))_m) tack.r cal(R) e : A + B$, $Gamma^(upright(bold(q))_l) \, x : A tack.r cal(R) a : C Gamma^(upright(bold(q))_l) \, y : B tack.r cal(R) b : C$, $Gamma^(upright(bold(q))_r) \, z : C tack.r cal(R) d : D$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) z = sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } ; #h(0em) d approx sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : sans(l e t) #h(0em) z = a ; #h(0em) d \, iota_r #h(0em) y : sans(l e t) #h(0em) z = b ; #h(0em) d } : D$)),
)
#rule-set(
  prooftree(rule(label: msc("let2-bind"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : A ⊗ B$, $Gamma^(upright(bold(q))_l) \, x : A \, y : B tack.r epsilon.alt c : C$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) c approx sans(l e t) #h(0em) z = a ; #h(0em) sans(l e t) #h(0em) \( x \, y \) = z ; #h(0em) c : C$)),
  prooftree(rule(label: msc("case-bind"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r cal(R) e : A + B$, $Gamma^(upright(bold(q))_l) \, x : A tack.r cal(R) a : C$, $Gamma^(upright(bold(q))_l) \, y : B tack.r cal(R) b : C$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } approx sans(l e t) #h(0em) z = e ; #h(0em) sans(c a s e) #h(0em) z #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } : C$)),
  prooftree(rule(label: msc("iter-bind"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $sans(q) \( Gamma^(upright(bold(q))_l) \) = top$, $epsilon.alt in cal(E)^oo$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_l) \, x : A tack.r epsilon.alt b : B + A$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : b } approx sans(l e t) #h(0em) y = a ; #h(0em) sans(i t e r) #h(0em) y #h(0em) { iota_r #h(0em) x : b } : B$)),
)

  ]],
  caption: [
    Binding rules for $lambda_(sans(i t e r))$
  ]
)
<refall:fig:binding-rules>

#figure([#block[
#rule-set(
  prooftree(rule(label: msc("term"), $Gamma^(upright(bold(q))) tack.r epsilon.alt a : upright(bold(1))$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) x = a ; #h(0em) \( \) approx a : upright(bold(1))$)),
  prooftree(rule(label: msc("elim"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))$, $Gamma^(upright(bold(q))_l) tack.r epsilon.alt a : upright(bold(1))$, $0 lt.eq sans(q)^p \( epsilon.alt \)$, $Gamma^(upright(bold(q))) tack.r eta b : B$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) x = a ; #h(0em) b arrow.r.twohead^p sans(l e t) #h(0em) x = \( \) ; #h(0em) b : B$)),
  prooftree(rule(label: msc("init"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : upright(bold(0))$, $Gamma^(upright(bold(q))_l) \, x : A tack.r epsilon.alt b : B$, $Gamma^(upright(bold(q))_l) \, x : A tack.r epsilon.alt b' : B$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) x = sans(a b o r t) #h(0em) a ; #h(0em) b approx sans(l e t) #h(0em) x = sans(a b o r t) #h(0em) a ; #h(0em) b' : B$)),
  prooftree(rule(label: msc("let2-eta"), $Gamma^(upright(bold(q))) tack.r epsilon.alt a : A ⊗ B$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) \( x \, y \) = a ; #h(0em) \( x \, y \) approx a : A ⊗ B$)),
  prooftree(rule(label: msc("let2-beta"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma tack.r upright(bold(q))_l = upright(bold(q))_a + upright(bold(q))_b$, $Gamma^(upright(bold(q))_a) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_b) tack.r epsilon.alt b : B$, $Gamma^(upright(bold(q))_r) \, x : A \, y : B tack.r epsilon.alt c : C$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) \( x \, y \) = \( a \, b \) ; #h(0em) c approx sans(l e t) #h(0em) x = a ; #h(0em) sans(l e t) #h(0em) y = b ; #h(0em) c : C$)),
  prooftree(rule(label: msc("case-betal"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r cal(R) e : A$, $Gamma^(upright(bold(q))_l) \, x : A tack.r cal(R) a : C$, $Gamma^(upright(bold(q))_l) \, y : B tack.r cal(R) b : C$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(c a s e) #h(0em) iota_l #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } approx sans(l e t) #h(0em) x = e ; #h(0em) a : C$)),
  prooftree(rule(label: msc("case-betar"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_r) tack.r cal(R) e : B$, $Gamma^(upright(bold(q))_l) \, x : A tack.r cal(R) a : C$, $Gamma^(upright(bold(q))_l) \, y : B tack.r cal(R) b : C$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(c a s e) #h(0em) iota_r #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b } approx sans(l e t) #h(0em) y = e ; #h(0em) b : C$)),
  prooftree(rule(label: msc("case-eta"), $Gamma^(upright(bold(q))) tack.r cal(R) e : A + B$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(c a s e) #h(0em) e #h(0em) { iota_l #h(0em) x : iota_l #h(0em) x \, iota_r #h(0em) y : iota_r #h(0em) y } approx e : A + B$)),
  prooftree(rule(label: msc("let1-beta^p"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $Gamma^(upright(bold(q))_l) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_r) \, x : A^q tack.r eta b : B$, $epsilon.alt harpoon.rt eta$, $q lt.eq sans(q) \( Gamma^(upright(bold(q))_r) \) ∩ sans(q)^p \( epsilon.alt \)$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) x = a ; #h(0em) b arrow.r.twohead^p \[ x \/ a \] b : B$)),
)

  ]],
  caption: [
    Reduction rules for $lambda_(sans(i t e r))$
  ]
)
<refall:fig:reduction-rules>

#figure([#block[
#rule-set(
  prooftree(rule(label: msc("iter-beta"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $sans(q) \( Gamma^(upright(bold(q))_l) \) = top$, $epsilon.alt in cal(E)^oo$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_l) \, x : A tack.r epsilon.alt b : B + A$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : b } approx sans(l e t) #h(0em) x = a ; #h(0em) sans(c a s e) #h(0em) b #h(0em) { iota_l #h(0em) y : y \, iota_r #h(0em) z : sans(i t e r) #h(0em) z #h(0em) { iota_r #h(0em) x : b } } : B$)),
  prooftree(rule(label: msc("let-iter"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_c Gamma tack.r upright(bold(q))_c = upright(bold(q))_m + upright(bold(q))_r$, $sans(q) \( Gamma^(upright(bold(q))_l) \) = top sans(q) \( Gamma^(upright(bold(q))_m) \) = top$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_m) \, x : A tack.r epsilon.alt b : B + A$, $Gamma^(upright(bold(q))_l) \, y : B tack.r epsilon.alt c : C$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) y = sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : b } ; #h(0em) c approx sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : sans(c a s e) #h(0em) b #h(0em) { iota_l #h(0em) y : iota_l #h(0em) c \, iota_r #h(0em) z : iota_r #h(0em) z } } : C$)),
  prooftree(rule(label: msc("codiag"), $Gamma tack.r upright(bold(q)) = upright(bold(q))_l + upright(bold(q))_r$, $sans(q) \( Gamma^(upright(bold(q))_l) \) = top$, $epsilon.alt in cal(E)^oo$, $Gamma^(upright(bold(q))_r) tack.r epsilon.alt a : A$, $Gamma^(upright(bold(q))_l) \, y : A tack.r epsilon.alt b : \( B + A \) + A$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : sans(i t e r) #h(0em) x #h(0em) { iota_r #h(0em) y : b } } approx sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) y : sans(c a s e) #h(0em) b #h(0em) { iota_l #h(0em) x : x \, iota_r #h(0em) y : iota_r #h(0em) y } } : B$)),
)
#rule-set(
  prooftree(rule(label: msc("unif^p"), $eta harpoon.rt epsilon.alt$, $Gamma^(upright(bold(q))_c) \, x : A tack.r cal(R) sans(l e t) #h(0em) y = s ; #h(0em) b arrow.r.twohead^p sans(c a s e) #h(0em) b' #h(0em) { iota_l #h(0em) z : iota_l #h(0em) c \, iota_r #h(0em) x : iota_r #h(0em) s } : C + S$, $Gamma^(upright(bold(q))) tack.r cal(R) sans(l e t) #h(0em) x = a ; #h(0em) sans(i t e r) #h(0em) s #h(0em) { iota_r #h(0em) y : b } arrow.r.twohead^p sans(l e t) #h(0em) z = sans(i t e r) #h(0em) a #h(0em) { iota_r #h(0em) x : b' } ; #h(0em) c : C$)),
)

  ]],
  caption: [
    Iteration rules for $lambda_(sans(i t e r))$
  ]
)
<refall:fig:iteration-rules>

#figure([],
  caption: [
    Control-flow graphs for the uniformity rule in
    Figure~@refall:fig:iteration-rules
  ]
)
<refall:fig:unif-cfg>

#hide(bibliography("/thesis/refs.bib", full: false))
