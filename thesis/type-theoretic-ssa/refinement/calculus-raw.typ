// Mechanical transcription from:
// papers/isotope/complete-refinement-ssa.tex
// Repository commit: 9480278f2503902f0fa632d05d7f0c8faae893f3
// Sections: Introduction; SSA; lambda_iter syntax, typing, metatheory, and refinement
// Source lines: 277--295 and 326--1652
// Conversion: prose preserved verbatim; LaTeX presentation translated mechanically to Typst.

#import "/lib/prelude.typ": *

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
memory];~@batty-compositional-17. This means memory can no longer be
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
is one that compiler writers struggle with~@llvm-github, because the
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
@appel-ssa: each basic block (or tail-recursive function!) takes a list
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

#figure([#figure([#block[
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
    minipage=1.2,scale=0.8 \$\$\\begin{aligned}
          {\\ensuremath{\\mathsf{start}}}:\\quad  & \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;n = 10; \\\\
                              & \\textcolor{violet}{\\ensuremath{\\mathsf{br}}}\\;\\ensuremath{\\mathsf{loop}} \\\\
          {\\ensuremath{\\mathsf{loop}}}: \\quad  & \\begingroup \\color{red}
                                \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;i\_0 = \\phi(\\ensuremath{\\mathsf{start}}: 1, \\ensuremath{\\mathsf{body}}: i\_1) 
                              \\endgroup \\\\
                              & \\begingroup \\color{blue}
                                \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;a\_0 = \\phi(\\ensuremath{\\mathsf{start}}: 1, \\ensuremath{\\mathsf{body}}: a\_1) 
                              \\endgroup \\\\
                              & \\textcolor{violet}{\\ensuremath{\\mathsf{if}}}\\;i\_0 \< n\\;\\{\\;\\textcolor{violet}{\\ensuremath{\\mathsf{br}}}\\;{\\ensuremath{\\mathsf{body}}}\\;\\} \\\\
                              & \\textcolor{violet}{\\ensuremath{\\mathsf{else}}}\\;\\{\\;\\textcolor{violet}{\\ensuremath{\\mathsf{ret}}}\\;a\_0\\;\\} \\\\
          {\\ensuremath{\\mathsf{body}}}: \\quad  & \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;t = i\_0 + 1 \\\\
                              & \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;a\_1 = a\_0 \* t \\\\
                              & \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;i\_1 = i\_0 + 1 \\\\
                              & \\textcolor{violet}{\\ensuremath{\\mathsf{br}}}\\;{\\ensuremath{\\mathsf{loop}}} \\\\ \\\\
        
    \\end{aligned}\$\$

    ]],
    caption: [
      $phi.alt$-nodes
    ]
  )
  <refall:fig:fact-phi>

  #figure([#block[
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
    minipage=1.2,scale=0.8 \$\$\\begin{aligned}
          {\\ensuremath{\\mathsf{start}}}:\\quad            & \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;n = 10; \\\\
                                        & \\textcolor{violet}{\\ensuremath{\\mathsf{br}}}\\;
                                            {\\ensuremath{\\mathsf{loop}}}(\\textcolor{red}{1}, \\textcolor{blue}{1}) \\\\
          {\\ensuremath{\\mathsf{loop}}}(\\textcolor{red}{i\_0}, \\textcolor{blue}{a\_0}): \\quad  
                                        & \\textcolor{violet}{\\ensuremath{\\mathsf{if}}}\\;i\_0 \< n\\; \\{\\;\\textcolor{violet}{\\ensuremath{\\mathsf{br}}}\\;{\\ensuremath{\\mathsf{body}}}\\;\\} \\\\
                                        & \\textcolor{violet}{\\ensuremath{\\mathsf{else}}}\\;\\{\\;\\textcolor{violet}{\\ensuremath{\\mathsf{ret}}}\\;a\_0\\;\\} \\\\
          {\\ensuremath{\\mathsf{body}}}: \\quad            & \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;t = i\_0 + 1 \\\\
                                        & \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;a\_1 = a\_0 \* t \\\\
                                        & \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;i\_1 = i\_0 + 1 \\\\
                                        & \\textcolor{violet}{\\ensuremath{\\mathsf{br}}}\\;{\\ensuremath{\\mathsf{loop}}}
                                          (\\textcolor{red}{i\_1}, \\textcolor{blue}{a\_1}) 
                                        \\\\ \\\\ \\\\ \\\\
        
    \\end{aligned}\$\$

    ]],
    caption: [
      Basic-blocks with arguments
    ]
  )
  <refall:fig:fact-bba>

  #figure([#block[
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
    minipage=,scale=0.8 \$\$\\begin{aligned}
          & \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;n = 10; \\\\
          & \\textcolor{violet}{\\ensuremath{\\mathsf{br}}}\\;{\\ensuremath{\\mathsf{loop}}}(\\textcolor{red}{1}, \\textcolor{blue}{1}) \\\\
          & \\textcolor{violet}{\\ensuremath{\\mathsf{where}}}\\;{\\ensuremath{\\mathsf{loop}}}(\\textcolor{red}{i\_0}, \\textcolor{blue}{a\_0}): \\{ \\\\
          & \\quad \\textcolor{violet}{\\ensuremath{\\mathsf{if}}}\\;i\_0 \< n\\;\\{\\;\\textcolor{violet}{\\ensuremath{\\mathsf{br}}}\\;{\\ensuremath{\\mathsf{body}}}\\;\\} \\\\
          & \\quad \\textcolor{violet}{\\ensuremath{\\mathsf{else}}}\\;\\{\\;\\textcolor{violet}{\\ensuremath{\\mathsf{ret}}}\\;a\_0\\;\\} \\\\
          & \\quad \\textcolor{violet}{\\ensuremath{\\mathsf{where}}}\\;{\\ensuremath{\\mathsf{body}}}: \\{\\\\ 
          & \\qquad \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;t = i\_0 + 1 \\\\
          & \\qquad \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;a\_1 = a\_0 \* t \\\\
          & \\qquad \\textcolor{violet}{\\ensuremath{\\mathsf{let}}}\\;i\_1 = i\_0 + 1 \\\\
          & \\qquad \\textcolor{violet}{\\ensuremath{\\mathsf{br}}}\\;{\\ensuremath{\\mathsf{loop}}}(\\textcolor{red}{i\_1}, \\textcolor{blue}{a\_1})  \\\\
          & \\quad \\} \\\\
          & \\}
        
    \\end{aligned}\$\$

    ]
    ],
    caption: [
      Lexical scoping
    ]
  )
  ],
  caption: [
    A program to compute $10 !$ written in standard SSA (using $phi.alt$
    nodes), like in LLVM @llvm, and using basic-blocks with arguments,
    like in MLIR @mlir and Cranelift @cranelift, with both implicit
    (dominance-based) and explicit (lexical) scoping. The arguments
    $i_0 \, a_0$ corresponding to the $phi.alt$-nodes $i_0 \, a_0$ are
    colored in red and blue, respectively.
  ]
)
<refall:fig:fact-lex>

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
Subsection~@refall:ssec:interconversion that the two syntaxes are completely
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
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
defined as follows: \$\$\\begin{gathered}
  \\prftree\[r\]{{\\scriptsize\\textsf{nil}}}{\\cdot \\mapsto \\cdot} \\qquad 
  \\prftree\[r\]{{\\scriptsize\\textsf{cons}}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\mapsto \\Delta^{\\ensuremath{\\mathbf{q}}\'}}
    {q\' \* \\ensuremath{\\mathsf{q}}(A) \\leq q \* \\ensuremath{\\mathsf{q}}(A)}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}}, x : A^q \\mapsto \\Delta^{\\ensuremath{\\mathbf{q}}\'}, x : A^{q\'}} \\qquad
  \\prftree\[r\]{{\\scriptsize\\textsf{skip}}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\mapsto \\Delta^{\\ensuremath{\\mathbf{q}}\'}}
    {0\\leq q \* \\ensuremath{\\mathsf{q}}(A)}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}}, x : A^q \\mapsto \\Delta^{\\ensuremath{\\mathbf{q}}\'}}
\\end{gathered}\$\$ To define weakening, we extend the meet on $Q$ to a
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
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
as follows: \$\$\\begin{gathered}
  \\prftree\[r\]{{\\scriptsize\\textsf{nil}}}
    {\\cdot \\vdash \\cdot = \\cdot + \\cdot} \\qquad
  \\prftree\[r\]{{\\scriptsize\\textsf{both}}}
    {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
    {\\omega^+\\leq q \\sqcap \\ensuremath{\\mathsf{q}}(A)}
    {\\Gamma, x : A \\vdash (\\ensuremath{\\mathbf{q}}, q) = (\\ensuremath{\\mathbf{q}}\_l, q) + (\\ensuremath{\\mathbf{q}}\_r, q)}
    \\\\
  \\prftree\[r\]{{\\scriptsize\\textsf{left}}}
    {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
    {\\Gamma, x : A \\vdash (\\ensuremath{\\mathbf{q}}, q) = (\\ensuremath{\\mathbf{q}}\_l, q) + (\\ensuremath{\\mathbf{q}}\_r, 0)} \\qquad
  \\prftree\[r\]{{\\scriptsize\\textsf{right}}}
    {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
    {\\Gamma, x : A \\vdash (\\ensuremath{\\mathbf{q}}, q) = (\\ensuremath{\\mathbf{q}}\_l, 0) + (\\ensuremath{\\mathbf{q}}\_r, q)}
\\end{gathered}\$\$ The rules left and right allow us to use a variable,
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
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  minipage=1.1,scale=0.9 \$\$\\begin{gathered}
      \\prftree\[r\]{{\\scriptsize\\textsf{var}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\mapsto x : A^1}
          {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} x: {A}} 
        \\qquad
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_1\$}}}{\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;b}: {B}}
        \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{op}}}{f : A \\to\_\\epsilon B}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} f\\;a: {B}}
        \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{inst}}}
        {f \\in \\ensuremath{\\mathcal{I}}}
        {\\ensuremath{\\mathsf{src}}(f) = A}
        {\\ensuremath{\\mathsf{trg}}(f) = B}
        {\\ensuremath{\\mathsf{eff}}(f) \\leq \\epsilon}
        {f : A \\to\_\\epsilon B}
        \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{unit}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\mapsto \\cdot}{\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} (): {\\ensuremath{\\mathbf{1}}}} 
        \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{pair}}}{\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} b: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} (a, b): {A \\otimes B}} \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_2\$}}}{\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{} a: {A \\otimes B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = a;\\;c}: {C}}
        \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{inl}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\iota\_l\\;{a}: {A + B}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{inr}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} b: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\iota\_r\\;{b}: {A + B}} \\qquad    
      \\prftree\[r\]{{\\scriptsize\\textsf{abort}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} a: {\\ensuremath{\\mathbf{0}}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\ensuremath{\\mathsf{abort}}\\;{a}: {C}}
        \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{case}}}{\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} e: {A + B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} a: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\epsilon} b: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{x} :a, \\iota\_r\\;{y} :b\\}: {C}} \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{iter}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}) = \\omega}
        {\\epsilon \\in \\ensuremath{\\mathcal{E}}^\\infty}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\}: {B}}
    
  \\end{gathered}\$\$

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
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  minipage=1.1,scale=0.9 \$\$\\begin{gathered}
      \\prftree\[r\]{{\\scriptsize\\textsf{nil}}}{\\Gamma^{\\ensuremath{\\mathbf{q}}} \\mapsto \\cdot}
                                {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\cdot \\rhd \\cdot} \\qquad 
      \\prftree\[r\]{{\\scriptsize\\textsf{zero}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\sigma \\rhd \\Delta}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\sigma, x \\mapsto a \\rhd \\Delta^{\\ensuremath{\\mathbf{q}}\'}, x : A^0}
      \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{cons}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q\_l}}} \\vdash\_{\\epsilon\_l} \\sigma \\rhd \\Delta^{\\ensuremath{\\mathbf{q}}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon\_r} a: {A}}
        {q \\leq \\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_r})}
        {\\epsilon\_l \\rightleftharpoons\\epsilon\_r}
        {\\epsilon\_l, \\epsilon\_r \\leq \\epsilon}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} \\sigma, x \\mapsto a \\rhd \\Delta^{\\ensuremath{\\mathbf{q}}\'}, x : A^q}
    
  \\end{gathered}\$\$

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
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
have that \$\$\\prftree\[r\]{}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\bot} \\sigma \\rhd \\Delta^{\\ensuremath{\\mathbf{q}}\'}}
    {(\\Delta^{\\ensuremath{\\mathbf{q}}\'} \\vdash\_{} a \\twoheadrightarrow b : {A}) \\in \\ensuremath{\\mathcal{R}}}
    {(\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{} \[\\sigma\]a \\twoheadrightarrow\[\\sigma\]b : {A}) \\in \\ensuremath{\\mathcal{R}}}\$\$
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
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
\$\$\\begin{gathered}
  \\prftree\[r\]{{\\scriptsize\\textsf{base}}}
    {(\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{} a \\twoheadrightarrow b : {A}) \\in \\ensuremath{\\mathcal{R}}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow b : {A}} \\qquad
  \\prftree\[r\]{{\\scriptsize\\textsf{refl}}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} a: {A}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow a : {A}}
  \\qquad
  \\prftree\[r\]{{\\scriptsize\\textsf{trans}}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow b : {A}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} b \\twoheadrightarrow c : {A}}
    {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} a \\twoheadrightarrow c : {A}}
\\end{gathered}\$\$ The other congruence rules (in the appendix in
Figure~@refall:fig:congruence-refinement) correspond one-to-one with our term
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
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
\$\$\\prftree\[r\]{{\\scriptsize\\textsf{let\$\_1\$-\$\\beta\$}}}
  {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
  {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{\\epsilon} a: {A}}
  {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}, x : A^q \\vdash\_{\\eta} b: {B}}
  {\\epsilon \\rightleftharpoons\\eta}
  {q \\leq \\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}) \\sqcap \\ensuremath{\\mathsf{q}}(\\epsilon)}
  {
    \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;b} \\approx\[x/a\]b : {B}
  }\$\$ In particular, this obviously holds for pure expressions with
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
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  minipage=1.1,scale=0.9 \$\$\\begin{gathered}
      \\prftree\[r\]{{\\scriptsize\\textsf{let-op}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {f : A \\to\_\\epsilon B}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\epsilon} c: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = f\\;a;\\;c} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = f\\;x;\\;c}} : {C}}
        \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{let-let\$\_1\$}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_c + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_c = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_m}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_m}, x : A \\vdash\_{\\epsilon} b: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\epsilon} c: {C}}
        {
          \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = (\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;b});\\;c} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = b;\\;c}} : {C}
        }
        \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{let-let\$\_2\$}}}
        {
          \\prfStackPremises
          {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_c + \\ensuremath{\\mathbf{q}}\_r}
          {\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_c = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_m}
        }
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A \\otimes B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_m}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, z : C \\vdash\_{\\epsilon} d: {D}}
        {
          \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = (\\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = a;\\;c});\\;d} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = a;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = c;\\;d}} : {D}
        }
        \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{let-case}}}
        {
          \\prfStackPremises
          {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_c + \\ensuremath{\\mathbf{q}}\_r}
          {\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_c = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_m}
        }
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_m} \\vdash\_{\\ensuremath{\\mathcal{R}}} e: {A + B}}
        {
          \\prfStackPremises
          {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\ensuremath{\\mathcal{R}}} a: {C}}
          {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\ensuremath{\\mathcal{R}}} b: {C}}
        }
        {
          {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}, z : C \\vdash\_{\\ensuremath{\\mathcal{R}}} d: {D}}
        }
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = \\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{x} :a, \\iota\_r\\;{y} :b\\};\\;d} \\approx\\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{x} :\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = a;\\;d}, \\iota\_r\\;{y} :\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = b;\\;d}\\} : {D}
        } 
    
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  \\end{gathered}\$\$ \$\$\\begin{gathered}
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_2\$-bind}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A \\otimes B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}
        {
          \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = a;\\;c} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = a;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = z;\\;c}} : {C}
        } \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{case-bind}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\ensuremath{\\mathcal{R}}} e: {A + B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\ensuremath{\\mathcal{R}}} a: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\ensuremath{\\mathcal{R}}} b: {C}}
        {
          \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{x} :a, \\iota\_r\\;{y} :b\\} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = e;\\;\\ensuremath{\\mathsf{case}}\\;z\\;\\{\\iota\_l\\;{x} :a, \\iota\_r\\;{y} :b\\}} : {C}
        } \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{iter-bind}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}) = \\top}
        {\\epsilon \\in \\ensuremath{\\mathcal{E}}^\\infty}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = a;\\;\\ensuremath{\\mathsf{iter}}\\;y\\;\\{ \\iota\_r\\;{x} :b \\}} : {B}}
    
  \\end{gathered}\$\$

  ]],
  caption: [
    Binding rules for $lambda_(sans(i t e r))$
  ]
)
<refall:fig:binding-rules>

#figure([#block[
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  minipage=1.1,scale=0.9 \$\$\\begin{gathered}
      \\prftree\[r\]{{\\scriptsize\\textsf{term}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} a: {\\ensuremath{\\mathbf{1}}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;()} \\approx a : {\\ensuremath{\\mathbf{1}}}} \\qquad
      \\prftree\[r\]{{\\scriptsize\\textsf{elim}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{\\epsilon} a: {\\ensuremath{\\mathbf{1}}}}
        {0 \\leq \\ensuremath{\\mathsf{q}}^p(\\epsilon)}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\eta} b: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;b} \\twoheadrightarrow^{p} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = ();\\;b} : {B}}
      \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{init}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {\\ensuremath{\\mathbf{0}}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b\': {B}}
        {
          \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = \\ensuremath{\\mathsf{abort}}\\;{a};\\;b} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = \\ensuremath{\\mathsf{abort}}\\;{a};\\;b\'} : {B}
        } \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_2\$-\$\\eta\$}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\epsilon} a: {A \\otimes B}}
        {
          \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = a;\\;(x, y)} \\approx a : {A \\otimes B}
        } \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_2\$-\$\\beta\$}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_l = \\ensuremath{\\mathbf{q}}\_a + \\ensuremath{\\mathbf{q}}\_b}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_a} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_b} \\vdash\_{\\epsilon} b: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}, x : A, y : B \\vdash\_{\\epsilon} c: {C}}
        {
          \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;(x, y) = (a, b);\\;c} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;\\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = b;\\;c}} : {C}
        } \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{case-\$\\beta\_l\$}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\ensuremath{\\mathcal{R}}} e: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\ensuremath{\\mathcal{R}}} a: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\ensuremath{\\mathcal{R}}} b: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{case}}\\;\\iota\_l\\;{e}\\;\\{\\iota\_l\\;{x} :a, \\iota\_r\\;{y} :b\\} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = e;\\;a} : {C}
        } \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{case-\$\\beta\_r\$}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\ensuremath{\\mathcal{R}}} e: {B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\ensuremath{\\mathcal{R}}} a: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\ensuremath{\\mathcal{R}}} b: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{case}}\\;\\iota\_r\\;{e}\\;\\{\\iota\_l\\;{x} :a, \\iota\_r\\;{y} :b\\} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = e;\\;b} : {C}
        } \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{case-\$\\eta\$}}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} e: {A + B}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{case}}\\;e\\;\\{\\iota\_l\\;{x} :\\iota\_l\\;{x}, \\iota\_r\\;{y} :\\iota\_r\\;{y}\\} \\approx e : {A + B}
        } \\\\
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{let\$\_1\$-\$\\beta^p\$}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}, x : A^q \\vdash\_{\\eta} b: {B}}
        {\\epsilon \\rightharpoonup\\eta}
        {q \\leq \\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_r}) \\sqcap \\ensuremath{\\mathsf{q}}^p(\\epsilon)}
        {
          \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;b} \\twoheadrightarrow^{p} \[x/a\]b : {B}
        }
    
  \\end{gathered}\$\$

  ]],
  caption: [
    Reduction rules for $lambda_(sans(i t e r))$
  ]
)
<refall:fig:reduction-rules>

#figure([#block[
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  minipage=1.1,scale=0.9 \$\$\\begin{gathered}
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{iter-\$\\beta\$}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}) = \\top}
        {\\epsilon \\in \\ensuremath{\\mathcal{E}}^\\infty}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{\\epsilon} b: {B + A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\} \\approx\\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;\\ensuremath{\\mathsf{case}}\\;b\\;\\{\\iota\_l\\;{y} :y, \\iota\_r\\;{z} :\\ensuremath{\\mathsf{iter}}\\;z\\;\\{ \\iota\_r\\;{x} :b \\}\\}} : {B}}
      \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{let-iter}}}
        {
        \\prfStackPremises
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_c}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_c = \\ensuremath{\\mathbf{q}}\_m + \\ensuremath{\\mathbf{q}}\_r}
        }
        {
        \\prfStackPremises
        {\\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}) = \\top}
        {\\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_m}) = \\top}
        }
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_m}, x : A \\vdash\_{\\epsilon} b: {B + A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : B \\vdash\_{\\epsilon} c: {C}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b \\};\\;c} \\approx\\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :\\ensuremath{\\mathsf{case}}\\;b\\;\\{\\iota\_l\\;{y} :\\iota\_l\\;{c}, \\iota\_r\\;{z} :\\iota\_r\\;{z}\\} \\} : {C}
        } \\\\
      \\prftree\[r\]{{\\scriptsize\\textsf{codiag}}}
        {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_r}
        {\\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}) = \\top}
        {\\epsilon \\in \\ensuremath{\\mathcal{E}}^\\infty}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : A \\vdash\_{\\epsilon} b: {(B + A) + A}}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :\\ensuremath{\\mathsf{iter}}\\;x\\;\\{ \\iota\_r\\;{y} :b \\} \\} \\approx\\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{y} :\\ensuremath{\\mathsf{case}}\\;b\\;\\{\\iota\_l\\;{x} :x, \\iota\_r\\;{y} :\\iota\_r\\;{y}\\} \\} : {B}} \\\\
      % \\prftree\[r\]{\\rle{dist}}
      %   {
      %   \\prfStackPremises
      %   {\\qsp{\\Gamma}{\\mb{q}}{\\mb{q}\_l}{\\mb{q}\_c}}
      %   {\\qsp{\\Gamma}{\\mb{q}\_c}{\\mb{q}\_m}{\\mb{q}\_r}}
      %   }
      %   {\\alquant(\\Gamma^{\\mb{q}\_m}) = \\top}
      %   {\\hasty{\\Gamma^{\\mb{q}\_l}}{\\epsilon}{a}{A}}
      %   {\\hasty{\\Gamma^{\\mb{q}\_r}}{\\epsilon}{b}{B}}
      %   {\\hasty{\\Gamma^{\\mb{q}\_m}, y : B}{\\epsilon}{c}{C + B}}
      %   {
      %     % \\prfStackPremises
      %     % {\\Gamma^{\\mb{q}} \\vdash\_{\\mc{R}} (a, \\liter{b}{y}{c})}
      %     % {\\approx \\liter{(a, b)}{(x, y)}{\\caseexpr{c}{z}{\\linl{(x, z)}}{w}{\\linr{(x, w)}}} 
      %     % : A \\otimes C}
      %     \\tmeq{\\Gamma^{\\mb{q}}}{\\mc{R}}
      %       {(a, \\liter{b}{y}{c})}
      %       {\\liter{(a, b)}{(x, y)}{\\caseexpr{c}{z}{\\linl{(x, z)}}{w}{\\linr{(x, w)}}}}
      %       {A \\otimes C}
      %   }
    
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
  \\end{gathered}\$\$ \$\$\\begin{gathered}
#todo[Translate the adjacent exact-source LaTeX equation or figure fallback into native Typst; preserve its mathematical content.]
      \\prftree\[r\]{{\\scriptsize\\textsf{unif\$^p\$}}}
        {\\eta \\rightharpoonup\\epsilon}
        {\\Gamma^{\\ensuremath{\\mathbf{q}}\_c}, x : A \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;y = s;\\;b} \\twoheadrightarrow^{p} \\ensuremath{\\mathsf{case}}\\;b\'\\;\\{\\iota\_l\\;{z} :\\iota\_l\\;{c}, \\iota\_r\\;{x} :\\iota\_r\\;{s}\\} : {C + S}}
        {
          \\Gamma^{\\ensuremath{\\mathbf{q}}} \\vdash\_{\\ensuremath{\\mathcal{R}}} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;x = a;\\;\\ensuremath{\\mathsf{iter}}\\;s\\;\\{ \\iota\_r\\;{y} :b \\}} \\twoheadrightarrow^{p} \\ensuremath{\\ensuremath{\\mathsf{let}}\\;z = \\ensuremath{\\mathsf{iter}}\\;a\\;\\{ \\iota\_r\\;{x} :b\' \\};\\;c} : {C}
        } \\\\
      \\text{where} \\qquad {\\Gamma \\vdash \\ensuremath{\\mathbf{q}} = \\ensuremath{\\mathbf{q}}\_c + \\ensuremath{\\mathbf{q}}\_r} \\qquad
      {\\Gamma \\vdash \\ensuremath{\\mathbf{q}}\_c = \\ensuremath{\\mathbf{q}}\_l + \\ensuremath{\\mathbf{q}}\_c} \\qquad
      \\ensuremath{\\mathsf{q}}(\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}) = \\top \\qquad
      \\epsilon \\in \\ensuremath{\\mathcal{E}}^\\infty \\qquad
      {\\Gamma^{\\ensuremath{\\mathbf{q}}\_r} \\vdash\_{\\epsilon} a: {A}}
      \\\\
      \\qquad {\\Gamma^{\\ensuremath{\\mathbf{q}}\_c}, x : A \\vdash\_{\\eta} s: {S}}
      \\qquad {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, y : S \\vdash\_{\\epsilon} b: {C + A}}
      \\qquad {\\Gamma^{\\ensuremath{\\mathbf{q}}\_l}, x : A \\vdash\_{} b\': {B + A}}
      \\qquad {\\Gamma^{\\ensuremath{\\mathbf{q}}\_c}, z : B \\vdash\_{} c: {C}}
    
  \\end{gathered}\$\$

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
