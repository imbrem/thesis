// Verbatim mechanical transcription from:
// papers/isotope/denotational-semantics-of-ssa.tex
// Repository commit: afa82558acf643f53a3e038e635ed9520ace88c6
// Source sections: Static Single Assignment Form, lines 407–1221

#import "/lib/prelude.typ": *
#show: chapter.with(title: [#lssa: Static Single Assignment Form])

= Static Single Assignment Form
<static-single-assignment-form>
== From Three Address Code to SSA
<ssec:3addr-ssa>
Directly optimizing a source language can be difficult, because surface
languages are often very large and have features (such as type inference
and overloading) which make it difficult to express sound program
equivalences. Elaborating a surface language to a simpler intermediate
representation makes it easier to write program analyses and
optimizations. One of the earliest compiler IRs introduced is
#emph[three-address code]~@allen-70-cfa (also known as #emph[register
transfer language (RTL)]).

3-address programs consists of a #emph[control-flow graph] (CFG) $G$
with a distinguished, nameless entry block. Each node of the CFG
corresponds to a #emph[basic block] $beta$, which is a straight-line
sequence of #emph[instructions] $x = f \( y \, z \)$ (hence the name
#emph[3-address code], referring to the typical three variables
$x \, y \, z$) followed by a #emph[terminator] $tau$, which can be a
(conditional) branch to another basic block. We give a grammar for
3-address code in @fig:3addr-grammar, with some slight
adjustments to the usual presentation:

- #emph[Constants] $c$ are interpreted as nullary instructions
  $c \( \)$.

- We only support nullary tuples $\( \)$ and binary tuples
  $\( v \, v' \)$ as composite values; $n$-ary tuples
  $\( x \, y \, z \)$ can be encoded as nested binary tuples
  $\( \( x \, y \) \, z \)$.

- We allow conditional branches
  $sans("if") #h(0em) o #h(0em) { tau } #h(0em) sans("else") #h(0em) { tau' }$
  to be #emph[nested]. This allows us to emulate switch-statements
  $sans("switch") \( o \) { c_1 : tau_1 \, . . . \, c_n : tau_n }$ as
  nested if-statements without introducing spurious basic blocks.
  Likewise, for uniformity, a return-statement may appear in the branch
  of a conditional branch.

#figure([#block[
  #block[
  \<$v$\> ::= $x$ | $\( v \, v' \)$ | $\( \)$

  \<$o$\> ::= $v$ | $f #h(0em) v$ | $iota_l #h(0em) v$ |
  $iota_r #h(0em) v$ | $sans("abort") #h(0em) v$

  \<$beta$\> ::= $x = o ; beta$ | $\( x \, y \) = o ; beta$ | $tau$

  \<$tau$\> ::= $sans("br") #h(0em) ell$ | $sans("ret") #h(0em) v$ |
  $sans("if") #h(0em) o #h(0em) { tau } #h(0em) sans("else") #h(0em) { tau' }$

  \<$G$\> ::= $beta$ | $G ; #h(0em) ell : beta$

  ]
  ]],
  caption: [
    Grammar for 3-address code
  ]
)
<fig:3addr-grammar>

As a concrete example, consider the simple imperative program to compute
$10 !$ given in @fig:fact-program. We can normalize our code into
3-address code, as in @fig:fact-3addr, by:

- Converting structured control flow (e.g., $sans("while")$) into
  unstructured jumps between basic blocks.

- Converting composite expressions like $a \* \( i + 1 \)$ into a
  sequence of definitions naming each subexpression. Here, expressions
  like $a + b$ are syntactic sugar for primitive operations
  $+ \( a \, b \)$.

#figure([#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  align: (left, top),
  [#semi-math-panel([$  & sans("let") #h(0em) n = 10 ;\
     & sans("let mut") #h(0em) i = 1 ;\
     & sans("let mut") #h(0em) a = 1 ;\
     & sans("while") #h(0em) i < n #h(0em) {\
     & quad a = a \* \( i + 1 \)\
     & quad i = i + 1 ;\
     & }\
     & sans("ret") #h(0em) a\
     $],
    caption: [As an imperative program],
    numbering: "(a)",
  )
  <fig:fact-imp>],

  [#semi-math-panel([$  & n = 10 ;\
     & i = 1 ;\
     & a = 1 ;\
     & sans("br") #h(0em) sans("loop") ;\
    sans("loop") : quad & sans("if") #h(0em) i < n #h(0em) { #h(0em) sans("br") #h(0em) sans("body") #h(0em) } #h(0em) sans("else") #h(0em) { #h(0em) sans("ret") #h(0em) a #h(0em) } ;\
    sans("body") : quad & t = i + 1 ;\
     & a = a \* t ;\
     & i = i + 1 ;\
     & sans("br") #h(0em) sans("loop") $],
    caption: [As 3-address code],
    numbering: "(a)",
  )
  <fig:fact-3addr>],

  )

  ],
  caption: [
    A simple, slightly suboptimal program to compute $10 !$ via
    multiplication in a loop, represented as typical imperative code and
    in 3-address code.
  ]
)
<fig:fact-program>

While functional languages typically rely on #emph[lexical scoping],
where the scope of a variable is determined by its position within the
code's nested structure, 3-address code uses a different scoping
mechanism based on #emph[dominance]. In particular, a variable $x$ is
considered to be in scope at a specific point $P$ if and only if all
execution paths from the program's entry point to $P$ pass through a
definition $D$ for $x$. In this case, we say that the definition $D$
#emph[dominates] $P$. The relation on basic blocks “$A$ dominates $B$\"
can in fact be viewed as a tree rooted at the entry block: every pair of
basic blocks $A \, B$ have a least common ancestor $C$ which dominates
them both; we call this tree the #emph[dominator tree]
@cytron-ssa-intro-91.

Even though three address code was designed to simplify flow analysis,
many optimizations remain difficult to express in this format. Because a
variable's value may be set by multiple definitions throughout the
program's execution, variables do not have stable values, and so it is
not in general safe to substitute a definition for a variable. To
improve our ability to reason about programs, we introduce the
#emph[static single assignment] restriction, originally proposed by
#cite(<alpern-ssa-original-88>, form: "prose"), which states that every
variable must be defined at exactly one point in the program. Because
there is a unique definition for each variable, substitution is valid.

We can we intuitively think of each variable as being defined by an
immutable $sans("let")$-binding, and a variable $x$ is in scope at a
program point $P$, if and only if it sunique definition site $D_x$
strictly dominates $P$.

A given basic block can be converted to SSA form by numbering each
definition of a variable, effectively changing references to $x$ to
references to $x_t$, i.e. "$x$ at time $t$." For example, we could
rewrite
#align(center, grid(
  columns: (auto, auto, auto),
  column-gutter: 1.5em,
  row-gutter: 0.25em,
  $x = 3y + 5;$, [], $sans("let") med x_0 = 3y + 5;$,
  $x = 3x + 2;$, $approx$, $sans("let") med x_1 = 3x_0 + 2;$,
  $sans("ret") med (3x + 1)$, [], $sans("ret") med (3x_1 + 1)$,
))
This transformation enables algebraic reasoning about
expressions involving each $x_t$. However, since we can only define a
variable once in SSA form, expressing programs with loops and branches
becomes challenging. For example, naïvely trying to lower the program in
@fig:fact-3addr into SSA form would not work, since the reference
to $i$ in the right-hand-side of the statement $i = i + 1$ can refer to
#emph[either] the previous value of $i$ from the last iteration of the
loop #emph[or] the original value $i = 1$. The classical solution is to
introduce #emph[$phi.alt$-nodes], which select a value based on the
predecessor block from which control arrived. We give the lowering of
our program into SSA with $phi.alt$-nodes in @fig:fact-ssa.

#cite(<cytron-ssa-intro-91>, form: "prose") introduced the first
efficient algorithm to lower a program in 3-address code to valid SSA
while introducing a minimum number of $phi.alt$-nodes, making SSA
practical for widespread use as an intermediate representation.
Unfortunately, $phi.alt$-nodes do not have an obvious operational
semantics.

Additionally, they require us to adopt more complex scoping rules than
simple dominance-based scoping. For example, in the basic block
$sans("loop")$ in @fig:fact-ssa, $i_0$ evaluates to 1 if we came
from the entry block and to $i_1$ if we came from $sans("body")$.
Similarly, $a_0$ evaluates to either 1 or $a_1$ based on the predecessor
block. This does not obey dominance-based scoping, since $i_0$ and $i_1$
are defined #emph[after] the $phi.alt$-nodes $i_0$, $a_0$ that reference
them, which seems counterintuitive -- after all, variables are typically
used after they are defined. In fact, since the value of a
$phi.alt$-node is determined by which basic block is our immediate
predecessor, we instead need to use the rule that expressions in
$phi.alt$-node branches with source $S$ can use any variable $y$ defined
at the #emph[end] of $S$. Note that this is a strict superset of the
variables visible for a normal instruction $x$, which can only use
variables $y$ which #emph[dominate] $x$ -- i.e., such that #emph[every]
path from the entry block to the definition of $x$ goes through $y$,
rather than only those paths which also go through $S$.

#figure([#figure([$  & n = 10 ;\
     & i = 1 ;\
     & a = 1 ;\
     & sans("br") #h(0em) sans("loop") ;\
    sans("loop") : quad & sans("if") #h(0em) i < n #h(0em) { #h(0em) sans("br") #h(0em) sans("body") #h(0em) } #h(0em) sans("else") #h(0em) { #h(0em) sans("ret") #h(0em) a #h(0em) } ;\
    sans("body") : quad & sans("let") #h(0em) t = i + 1 ;\
     & a = a \* t ;\
     & i = i + 1 ;\
     & sans("br") #h(0em) sans("loop") $

    ],
    caption: [
      3-address code
    ]
  )

  #figure([$  & sans("let") #h(0em) n = 10 ;\
     & sans("br") #h(0em) sans("loop")\
    sans("loop") : quad & sans("let") #h(0em) i_0 = phi.alt \( sans("entry") : 1 \, sans("body") : i_1 \) ;\
     & sans("let") #h(0em) a_0 = phi.alt \( sans("entry") : 1 \, sans("body") : a_1 \) ;\
     & sans("if") #h(0em) i_0 < n #h(0em) { #h(0em) sans("br") #h(0em) sans("body") #h(0em) } #h(0em) sans("else") #h(0em) { #h(0em) sans("ret") #h(0em) a_0 #h(0em) } ;\
    sans("body") : quad & sans("let") #h(0em) t = i_0 + 1\
     & sans("let") #h(0em) a_1 = a_0 \* t\
     & sans("let") #h(0em) i_1 = i_0 + 1\
     & sans("br") #h(0em) sans("loop") $

    ],
    caption: [
      Converted to SSA form
    ]
  )
  <fig:fact-ssa>

  ],
  caption: [
    Conversion of three address code for the program in
    @fig:fact-program to SSA form, requring the insertion of
    $phi.alt$-nodes for $i$ and $a$ due to control-flow dependent
    updates. Note how SSA-form can be viewed as "three address code in
    which all $sans("let")$-bindings are immutable."
  ]
)
// The source label fig:fact-ssa is attached to the right-hand subfigure above.

While this rule can be quite confusing, and in particular makes it
non-obvious how to assign an operational semantics to $phi.alt$-nodes,
the fact that the scoping for $phi.alt$-node branches is based on the
source block, rather than the block in which the $phi.alt$-node itself
appears, hints at a possible solution. By #emph[moving] the expression
in each branch to the #emph[call-site], we can transition to an
isomorphic syntax called basic blocks with arguments (BBA), as
illustrated in @fig:fact-bba. In this approach, each
$phi.alt$-node -- since it lacks side effects and has scoping rules
independent of its position in the basic block, depending only on the
source of each branch -- can be moved to the top of the block. This
reorganization allows us to treat each $phi.alt$-node as equivalent to
an argument for the basic block, with the corresponding values passed at
the jump site. Converting a program from BBA format back to standard SSA
form with $phi.alt$-nodes is straightforward: introduce a $phi.alt$-node
for each argument of a basic block, and for each branch corresponding to
the $phi.alt$-node, add an argument to the jump instruction from the
appropriate source block.

We give a formal grammar for basic blocks-with-arguments SSA in
@fig:bba-grammar #footnote[Many variants of SSA do not allow
variables to appear alone on the right-hand side of assignments, such as
$x = y ; beta$. We do not incorporate this restriction, though we could
by normalizing even further and substituting $\[ y \/ x \] beta$
instead.]. One of the other changes we make is replacing conditional
branches
$sans("if") #h(0em) o #h(0em) { tau } #h(0em) sans("else") #h(0em) { tau' }$
with #emph[case-statements]
$sans("case") #h(0em) o #h(0em) { iota_l #h(0em) y : tau \, iota_r #h(0em) z : tau' }$.
In particular, a case-statement
$sans("if") #h(0em) o #h(0em) { tau } #h(0em) sans("else") #h(0em) { tau' }$
may be desugared into a case-statement on a Boolean value
$o : upright(bold(1)) + upright(bold(1))$.

Note that this grammar no longer needs a separate terminator for
returns: we can treat the return point as a distinguished label (with
argument) that a program can jump to.

#figure([#block[
  #block[
  \<$v$\> ::= $x$ | $\( v \, v' \)$ | $\( \)$

  \<$o$\> ::= $v$ | $f #h(0em) v$ | $iota_l #h(0em) v$ |
  $iota_r #h(0em) v$ | $sans("abort") #h(0em) v$

  \<$beta$\> ::= $sans("let") #h(0em) x = o ; beta$ |
  $sans("let") #h(0em) \( x \, y \) = o ; beta$ | $tau$

  \<$tau$\> ::= $sans("br") #h(0em) ell #h(0em) o$ |
  $sans("case") #h(0em) o #h(0em) { iota_l #h(0em) y : tau \, iota_r #h(0em) z : tau' }$

  \<$G$\> ::= $G #h(0em) #h(0em) ell \( x \) : beta$ | $beta$

  ]
  ]],
  caption: [
    Grammar for basic blocks-with-arguments SSA
  ]
)
<fig:bba-grammar>

This allows us to use dominance-based scoping without any special cases
for $phi.alt$-nodes. When considering basic blocks, this means that a
variable is visible within the block $D$ where it is defined, starting
from the point of its definition. It continues to be visible in all
subsequent blocks $P$ that are strictly dominated by $D$ in the
control-flow graph (CFG). For example, in @fig:fact-bba:

- The entry block strictly dominates all other blocks by definition;
  thus, the variable $n$ is visible in $sans("loop")$ and
  $sans("body")$.

- $sans("loop")$ strictly dominates $sans("body")$; therefore, the
  parameters $i_0$, $a_0$ to $sans("loop")$ are visible in
  $sans("body")$ without the need to pass them as parameters.

- $sans("body")$ does #emph[not] strictly dominate $sans("loop")$,
  since there is a path from the entry block to $sans("loop")$ that
  does not pass through $sans("body")$.

#figure([#grid(
  columns: (1fr, 1fr),
  column-gutter: 1em,
  [#figure([#text(size: 8.5pt)[#grid(
      columns: (auto, auto),
      column-gutter: 0.7em,
      row-gutter: 0.18em,
      [], $sans("let") med n = 10;$,
      [], $sans("br") med sans("loop");$,
      [$sans("loop"):$], text(fill: red)[$sans("let") med i_0 = phi.alt(sans("entry"): 1, sans("body"): i_1);$],
      [], text(fill: blue)[$sans("let") med a_0 = phi.alt(sans("entry"): 1, sans("body"): a_1);$],
      [], $sans("if") med i_0 < n med {sans("br") med sans("body")}$,
      [], $sans("else") med {sans("ret") med a_0};$,
      [$sans("body"):$], $sans("let") med t = i_0 + 1$,
      [], $sans("let") med a_1 = a_0 times t$,
      [], $sans("let") med i_1 = i_0 + 1$,
      [], $sans("br") med sans("loop")$,
    )]],
    caption: [
      With $phi.alt$-nodes
    ]
  ) <fig:fact-phi>],

  [#figure([#text(size: 8.5pt)[#grid(
      columns: (auto, auto),
      column-gutter: 0.7em,
      row-gutter: 0.18em,
      [], $sans("let") med n = 10;$,
      [], [$sans("br") med sans("loop")(#text(fill: red)[$1$], #text(fill: blue)[$1$]);$],
      [#box[$sans("loop")(#text(fill: red)[$i_0$], #text(fill: blue)[$a_0$]):$]], $sans("if") med i_0 < n med {sans("br") med sans("body")}$,
      [], $sans("else") med {sans("ret") med a_0};$,
      [$sans("body"):$], $sans("let") med t = i_0 + 1$,
      [], $sans("let") med a_1 = a_0 times t$,
      [], $sans("let") med i_1 = i_0 + 1$,
      [], [$sans("br") med sans("loop")(#text(fill: red)[$i_1$], #text(fill: blue)[$a_1$])$],
    )]],
    caption: [
      Basic-blocks with arguments
    ]
  ) <fig:fact-bba>],
)],
  caption: [
    The program in @fig:fact-program written in standard SSA
    (using $phi.alt$ nodes), like in LLVM @llvm, and in basic-blocks
    with arguments SSA, like in MLIR @mlir and Cranelift @cranelift. The
    arguments $i_0 \, a_0$ corresponding to the $phi.alt$-nodes
    $i_0 \, a_0$ are colored in red and blue, respectively.
  ]
)
// The source label fig:fact-bba is attached to the right-hand subfigure above.

== Type-theoretic SSA
<ssec:tt-ssa>
An important insight provided by the BBA format, as discussed by
#cite(<appel-ssa>, form: "prose") and
#cite(<kelsey-95-cps>, form: "prose"), is that a program in SSA form
can be interpreted as a collection of tail-recursive functions, where
each basic block and branch correspond to a function and tail call,
respectively. This yields a natural framework for defining the semantics
of SSA and reasoning about optimizations.

A program in BBA is not quite a functional program, because scoping is
dominance-based rather than lexically scoped. However, it turns out to
be very easy to convert dominance-based scoping into lexical scoping.
Observe that the function corresponding to a given basic block $B$ can
only be called by other blocks $B'$ having that basic block's parent
$P = sans("parent") \( B \)$ as an ancestor in the dominance tree
(as, otherwise, the parent would not actually dominate the block, since
we could get to $B$ through $B'$ without passing through $P$). Moreover,
the variables #emph[visible] in $B$ are exactly the variables visible at
the end of $P$; i.e., the variables visible in $P$ and those defined in
$P$.

So if we make the dominance tree explicit in the syntax and tie the
binding of variables to this tree structure, then lexical and
dominance-based scoping become one and the same. We use this observation
to introduce #emph[lexical SSA] in @fig:lex-ssa. The key idea of
this syntax is to, rather than treating the control-flow graph $G$ as a
flat collection of basic blocks (with a distinguished block), to instead
consider (subtrees of) the dominance tree $r$, with the root of the tree
implicitly being the entry block. We call such subtrees #emph[regions]:
we note that they have a single entry (the root) and multiple exits (the
leaves), and so generalize the more standard concept of a
single-entry-single-exit region in a CFG.

In particular, a #emph[region] $r$ generalizes a basic block $beta$ by
annotating the terminator $tau$ with a list $L$ of #emph[labeled
branches] "$ell_i \( x_i \) : { t_i }$," yielding a
#emph[$sans("where")$-block]
"$tau #h(0em) sans("where") #h(0em) L$". Each $ell_i$ can only be
branched to by $tau$ and the regions $t_i$, thus syntactically enforcing
that the basic block at the root of $r$ (made up of its instructions and
terminators) #emph[dominates] all the basic blocks in the subregions
$t_i$ (which can only be reached through $r$). The data of a region $r$
is thus exactly the data contained in a basic block $beta$ (its
instructions and terminator) together with a set of subregions dominated
by $r$; in C++-like pseudocode, we might represent a region as in
@fig:ssa-data.

Regions allow us to enforce dominance-based scoping simply by making the
variables defined in $r$ visible only in the $t_i$, which, as previously
stated, #emph[must] be dominated by $r$; i.e., dominance based scoping
becomes lexical scoping of $sans("where")$-blocks. It is easy to see
(we demonstrate this more rigorously in
#todo[the future subsection `ssec:ssa-normal`]) that,
given a CFG $G$, there exists some way to annotate its topological sort
w.r.t. the dominance relation with $sans("where")$-blocks to obtain a
region $r$ which is lexically well-scoped if and only if $C$ is a valid
SSA program; we illustrate this process on our running example in
@fig:dominance-to-lexical. Conversely, erasing the
$sans("where")$-blocks from a region $r$ and giving the root a name
trivially yields a (topologically sorted!) SSA program, establishing an
isomorphism between lexical SSA and standard SSA.

#figure([#block[
  #block[
  \<$v$\> ::= $x$ | $\( v \, v' \)$ | $\( \)$

  \<$o$\> ::= $v$ | $f #h(0em) v$ | $iota_l #h(0em) v$ |
  $iota_r #h(0em) v$ | $sans("abort") #h(0em) v$

  \<$r \, s \, t$\> ::= $sans("let") #h(0em) x = o ; t$ |
  $sans("let") #h(0em) \( x \, y \) = o ; t$ |
  $tau #h(0em) sans("where") #h(0em) L$

  \<$tau$\> ::= $sans("br") #h(0em) ell #h(0em) o$ |
  $sans("case") #h(0em) o #h(0em) { iota_l #h(0em) y : tau \, iota_r #h(0em) z : tau' }$

  \<$L$\> ::= $dot.op$ | $L \, ell \( x \) : { t }$

  ]
  ]],
  caption: [
    Grammar for lexically-scoped SSA
  ]
)
<fig:lex-ssa>

#code-figure([```cpp
  struct BasicBlock {
        // unary/binary let-bindings, collected into a list
        vector<Instruction> instructions;             
        Terminator terminator;                        
        // Dominated basic blocks, forming a subtree of the dominance tree
        // Note that only `terminator` is allowed to jump to blocks in `children`
        map<Label, (Argument, BasicBlock)> children;  
      }
  ```

  ],
  caption: [
    Data encoded by the grammar in @fig:lex-ssa
  ]
)
<fig:ssa-data>

#figure([#figure([$  & sans("let") #h(0em) n = 10 ;\
     & sans("br") #h(0em) sans("loop") \( 1 \, 1 \)\
    sans("loop") \( i_0 \, a_0 \) : quad & sans("if") #h(0em) i_0 < n #h(0em) { #h(0em) sans("br") #h(0em) sans("body") #h(0em) }\
     & sans("else") #h(0em) { #h(0em) sans("ret") #h(0em) a_0 #h(0em) }\
    sans("body") : quad & sans("let") #h(0em) t = i_0 + 1\
     & sans("let") #h(0em) a_1 = a_0 \* t\
     & sans("let") #h(0em) i_1 = i_0 + 1\
     & sans("br") #h(0em) sans("loop") \( i_1 \, a_1 \)\
    \
    \
    \
     $

    ],
    caption: [
      Dominance-based scoping
    ]
  )

  #figure([$  & sans("let") #h(0em) n = 10 ;\
     & sans("br") #h(0em) sans("loop") \( 1 \, 1 \)\
     & sans("where") #h(0em) sans("loop") \( i_0 \, a_0 \) : {\
     & quad sans("if") #h(0em) i_0 < n #h(0em) { #h(0em) sans("br") #h(0em) sans("body") #h(0em) }\
     & quad sans("else") #h(0em) { #h(0em) sans("ret") #h(0em) a_0 #h(0em) }\
     & quad sans("where") #h(0em) sans("body") : {\
     & #h(2em) sans("let") #h(0em) t = i_0 + 1\
     & #h(2em) sans("let") #h(0em) a_1 = a_0 \* t\
     & #h(2em) sans("let") #h(0em) i_1 = i_0 + 1\
     & #h(2em) sans("br") #h(0em) sans("loop") \( i_1 \, a_1 \)\
     & quad }\
     & } $

    ],
    caption: [
      Lexical scoping
    ]
  ),
)

  ],
  caption: [
    Conversion of an SSA program from dominance-based scoping to
    explicit lexical scoping
  ]
)
<fig:dominance-to-lexical>

Lexical scoping allows us to apply many of techniques developed in type
theory and functional programming for reasoning about program
transformations. Indeed, the result of our conversion to lexical scoping
looks a lot like the correspondence between SSA and CPS described in
#cite(<kelsey-95-cps>, form: "prose"). We can use this correspondence
to guide us in developing an #emph[equational theory] for SSA programs,
with the goal of enabling compositional reasoning about program
transformations such as:

- #emph[Control-flow rewrites], such as jump-threading or fusing two
  identical branches of an $sans("if")$-statement

- #emph[Algebraic rewrites], such as simplifying arithmetic expressions

- Combinations of the two, such as rewriting
  "$sans("if") #h(0em) x > 0 #h(0em) sans("then") #h(0em) 0 - x #h(0em) sans("else") #h(0em) x$"
  to "$sans("abs") \( x \)$".

To help achieve this, we will slightly generalize our syntax by:

+ Fusing the syntactic categories $o \, v$ of operations and values into
  the syntactic category $a$ of #emph[expressions]
  #metadata(none) <ssa-change-val>

+ Fusing the syntactic category $tau$ of terminators into the syntactic
  category of regions $r$.
  #metadata(none) <ssa-change-reg>

+ Extending expressions $a$ to allow #emph[let-expressions]
  "$sans("let") #h(0em) x = a ; #h(0em) b$" and #emph[case-expressions]
  "$sans("case") #h(0em) a #h(0em) { iota_l #h(0em) x : b \, iota_r #h(0em) y : c }$"
  #metadata(none) <ssa-change-expr>

This leaves us with our final language, #lssa, the
resulting grammar for which is given in @fig:ssa-grammar. It is
easy to see that these changes add no expressive power to lexical SSA:
we can desugar #link(<ssa-change-val>)[1] by introducing names for anonymous
sub-expressions, #link(<ssa-change-reg>)[2] by introducing names for anonymous
sub-regions, and #link(<ssa-change-expr>)[3] by floating out let-bindings and
case-statements in the obvious manner, introducing labels as necessary;
we discuss this in more detail in
#todo[the future subsection `ssec:ssa-normal`].

Change #link(<ssa-change-val>)[1] allows us to effectively reason about
#emph[substitution]: replacing the value of a variable (which is a
value $v$) with its definition (which is an instruction $o$). This can
be used as a building block for optimizations such as common
subexpression elimination and global value numbering; combined with
change #link(<ssa-change-expr>)[3], we can also reason algebraically about
"branching" operations like conditional move and absolute value.

On the other hand, #link(<ssa-change-reg>)[2] lets us replace an unconditional
branch $sans("br") #h(0em) ell #h(0em) a$ (which is a terminator $tau$)
with the code #emph[pointed to] by the label $ell$ (which is a region
$r$), allowing us to perform the jump-threading optimization
$ sans("let") #h(0em) x = a ; sans("br") #h(0em) ell #h(0em) b #h(0em) sans("where") #h(0em) ell \( y \) : { r } approx sans("let") #h(0em) x = a ; sans("let") #h(0em) y = b ; r #h(0em) sans("where") #h(0em) ell \( y \) : { r } $
While both sides of this equation are valid lexical SSA programs, by
loosening our syntax slightly, we can #emph[unconditionally] replace
jumps with regions, without worrying about jumps nested in case
statements or fusing $sans("where")$-blocks. This, especially combined
with change #link(<ssa-change-expr>)[3], makes it much easier to verify
optimizations such as
$  & sans("case") #h(0em) a #h(0em) { iota_l #h(0em) x : sans("br") #h(0em) ell #h(0em) \( iota_r #h(0em) x \) \, iota_r #h(0em) x : sans("br") #h(0em) ell #h(0em) \( iota_l #h(0em) x \) } #h(0em) sans("where") #h(0em) ell \( y \) : { sans("case") #h(0em) y #h(0em) { iota_l #h(0em) z : sans("ret") #h(0em) \( iota_r #h(0em) z \) \, iota_r #h(0em) z : sans("ret") #h(0em) \( iota_l #h(0em) z \) } }\
 & approx sans("case") #h(0em) a #h(0em) { iota_l #h(0em) x : sans("case") #h(0em) iota_r #h(0em) x #h(0em) { iota_l #h(0em) z : sans("ret") #h(0em) \( iota_r #h(0em) z \) \, iota_r #h(0em) z : sans("ret") #h(0em) \( iota_l #h(0em) z \) }\
 & #h(2em) #h(0em) #h(0em) \, iota_r #h(0em) x : sans("case") #h(0em) iota_l #h(0em) x #h(0em) { iota_l #h(0em) z : sans("ret") #h(0em) \( iota_r #h(0em) z \) \, iota_r #h(0em) z : sans("ret") #h(0em) \( iota_l #h(0em) z \) } }\
 & approx sans("case") #h(0em) a #h(0em) { iota_l #h(0em) x : sans("ret") \( iota_l #h(0em) x \) \, iota_r #h(0em) x : sans("ret") \( iota_r #h(0em) x \) } approx sans("ret") #h(0em) \( sans("case") #h(0em) a #h(0em) { iota_l #h(0em) x : iota_l #h(0em) x \, iota_r #h(0em) x : iota_r #h(0em) x } \) approx sans("ret") #h(0em) a $
by repeatedly applying a set of known-good rules, and, moreover,
dramatically simplifies the form of the rules themselves.

#figure([#block[
  #block[
  \<$a \, b \, c \, e$\> ::= $x$ | $f #h(0em) a$ |
  $sans("let") #h(0em) x = a ; #h(0em) e$ $\( \)$ | $\( a \, b \)$ |
  $sans("let") #h(0em) \( x \, y \) = a ; #h(0em) e$ $iota_l #h(0em) a$
  | $iota_r #h(0em) a$ | $sans("abort") #h(0em) a$ |
  $sans("case") #h(0em) e #h(0em) { iota_l #h(0em) x : a \, iota_r #h(0em) y : b }$

  \<$r \, s \, t$\> ::= $sans("let") #h(0em) x = a ; t$ |
  $sans("let") #h(0em) \( x \, y \) = a ; t$ |
  $t #h(0em) sans("where") #h(0em) L$ |
  $sans("br") #h(0em) ell #h(0em) a$ |
  $sans("case") #h(0em) e #h(0em) { iota_l #h(0em) x : s \, iota_r #h(0em) y : t }$

  \<$L$\> ::= $dot.op$ | $L \, ell \( x \) : { t }$

  ]
  ]],
  caption: [
    Grammar for #lssa
  ]
)
<fig:ssa-grammar>

#standalone-bibliography()
