#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/simplebnf:0.1.1": *

#import "@preview/wordometer:0.1.5": word-count, total-words
#show: word-count.with(exclude: <no-wc>)

#let max-words = 60000
#let percent-done = context {
  calc.round(decimal((100 * state("wordometer").final().words) / max-words), digits: 3)
}
#let p-doom = context { 
  let prop-done = state("wordometer").final().words / max-words
  if prop-done > 0.9 {
    [*LOW*]
  } else if prop-done > 0.5 {
    [*MEDIUM*]
  } else {
    [*HIGH*]
  }
}

#import "thesis-template.typ": *
#import "todos.typ": todo, todo-inline, total-todos

#let ms(txt) = $sans(txt)$
#let mb(txt) = $bold(txt)$

#set text(lang: "en")

#set document(
  title: [Categorical imperative programming: 
    a type theory and denotational semantics for Static Single Assignment (SSA) form]
)

#title()

#align(center + horizon)[
  #todo("make a title page; preferably as a template")
]

#align(center + horizon)[
  *The current word count is* $#total-words slash #max-words ≈ #percent-done%$ complete.

  *There are $#total-todos$ TODOs remaining*

  $P(ms("doom"))$ is currently *#p-doom*
]

#pagebreak()

#statement-of-originality

#todo[What's the right way to format this?] 

#todo[Do we put the acknowledgements here or after the abstract?]

#pagebreak()

#align(center + horizon)[
  Is _this_ abstract enough?
  #todo[Actually write an abstract]
]

#pagebreak()

#outline()

#pagebreak()

= Introduction

#todo[start at the middle]

= Static Single Assignment (SSA)

== From RTL to SSA

/*
TRANSLATION NOTES: 
- We change references to 3-address code to RTL
- We try to split up paragraphs to be 1-idea-per-line in the source text 
  (this renders to the same output, but helps with version control/diffing)
*/

#todo[$n$-ary or binary presentation?]

Directly optimizing a source language can be difficult, 
  because surface languages are often very large and have features 
    (such as type inference and overloading) 
  which make it difficult to express sound program equivalences. 
Elaborating a surface language to a simpler intermediate representation makes it easier to write program analyses and optimizations. 
One of the earliest compiler IRs introduced is _register transfer language_ (_RTL_) @allen-70-cfa,
  commonly referred to as _three-address code_.

#let ite(o, l, r) = $ms("if") #o thick { #l } ms("else") { #r }$
#let linl(v) = $ι_l med #v$
#let linr(v) = $ι_r med #v$
#let labort(v) = $ms("abort") #v$
#let seq = $; thick$
#let brb(ℓ, v) = $ms("br") #ℓ thick #v$
#let retb(v) = $ms("ret") #v$
#let caseexpr2(e, x, a, y, b) = $ms("case") #e thick {linl(#x) : #a seq linr(#y) : #b}$
#let casestmt2(e, x, s, y, t) = $ms("case") #e thick {linl(#x) : #s seq linr(#y) : #t}$
#let wbranch(ℓ, x, t) = $#ℓ (#x) : #t$
#let where(t, L) = $#t thick ms("where") {#L}$
#let letstmt(x, a, t) = $ms("let") #x = #a; #t$
#let letexpr(x, a, e) = $ms("let") #x = #a; #e$

RTL programs consists of a _control-flow graph_ (CFG) $G$ 
  with a distinguished, nameless entry block. 
Each node of the CFG corresponds to a _basic block_ $β$, 
  which is a straight-line sequence of _instructions_ $x = f(y, z)$ 
    (hence the name _3-address code_, referring to the typical three variables $x, y, z$) 
  followed by a _terminator_ $τ$, 
    which can be a (conditional) branch to another basic block. 
We give a grammar for RTL code in @rtl-grammar, 
  with some slight adjustments to the usual presentation:

#todo[introduce destructures more smoothly? consider $n$-ary case?]

  #todo[mention that case statements can also be nested?]

- _Constants_ $c$ are interpreted as nullary instructions $c()$.
- _Conditional branches_ $ite(x, τ, τ')$ are desugared to 
    case-statements $casestmt2(x, y, τ, z, τ')$ on a Boolean $x : mb(1) + mb(1)$. 
  This is equivalent in power to regular conditional branches, 
    while allowing our work to generalize easily to higher-level settings as well.
- _Return statements_ $retb(v)$ are desugared to branches $brb(ℓ_ms("exit"), v)$ 
    to a distinguished exit label $ℓ_ms("exit")$. 
  In particular, 
    this allows a return-statement to appear in the branch of a case-statement or if-statement.

#figure(
  [
    #stack(
      dir: ltr,
      spacing: 3em,
      bnf(
        Prod(
          $v$,
          annot: $ms("Val")$,
          {
            Or[$x$][_variable_]
            Or[$(v, v')$][_tuple_]
            Or[$()$][_unit_]
          }
        )
      ),
      bnf(
        Prod(
          $o$,
          annot: $ms("Inst")$,
          {
            Or[$v$][_value_]
            Or[$f med v$][_operation_]
            Or[$linl(v)$][_left injection_]
            Or[$linr(v)$][_right injection_]
            Or[$labort(v)$][_abort_]
          }
        )
      )
    )
    #stack(
      dir: ltr,
      spacing: 3em,
      bnf(
        Prod(
          $β$,
          annot: $ms("BB")$,
          {
            Or[$x = o seq β$][_assign_]
            Or[$(x, y) = o seq β$][_destructure_]
            Or[$τ$][_terminator_]
          }
        )
      ),
      bnf(
        Prod(
          $τ$,
          annot: $ms("Trm")$,
          {
            Or[$brb(ℓ, o)$][_branch_]
            Or[$casestmt2(o, x, τ, y, τ')$][_case_]
          }
        )
      )
    )
    #bnf(
      Prod(
        $β$,
        annot: $ms("CFG")$,
        {
          Or[$β$][_entry block_]
          Or[$G seq ℓ : β$][_labeled basic block_]
        }
      )
    )
  ],
  caption: [Grammar for RTL],
  kind: image
) <rtl-grammar>

As a concrete example, consider the simple imperative program to compute $10!$ given in
Figure~#todo-inline("imperative factorial"). We can normalize our code into RTL, as in
Figure~#todo-inline("RTL factorial"), by:
- Converting structured control flow (e.g., $ms("while")$) into unstructured jumps between basic
blocks labelled $ms("start")$, $ms("loop")$, and $ms("body")$.
- Converting composite expressions like $a * (i + 1)$ into a sequence of definitions naming each
subexpression.

#todo[figure: imperative factorial]

#todo[figure: RTL factorial]

While functional languages typically rely on _lexical scoping_, 
  where the scope of a variable is determined by its position within the code's nested structure, 
  RTL uses a different scoping mechanism based on _dominance_. 
In particular, 
  a variable $x$ is considered to be in scope at a specific point $P$ 
    if and only if all execution paths from the program's entry point to $P$ 
      pass through a definition $D$ for $x$. 
In this case, we say that the definition $D$ _dominates_ $P$. 
The relation on basic blocks "$A$ dominates $B$" can in fact be viewed as a tree rooted at the entry block: 
  every pair of basic blocks $A, B$ have a least common ancestor $C$ which dominates them both; 
  we call this tree the _dominator tree_ @cytron-91-ssa-intro.

Even though three address code was designed to simplify flow analysis, 
  many optimizations remain difficult to express in this format. 
Because a variable's value may be set by multiple definitions throughout the program's execution, 
  variables do not have stable values, 
  and so it is not in general safe to substitute a definition for a variable. 
To improve our ability to reason about programs, 
  we introduce the _static single assignment_ restriction, 
    originally proposed by @alpern-88-ssa-original, 
  which states that every variable must be defined at exactly one point in the program. 
Because there is a unique definition for each variable, substitution is valid.

We can intuitively think of each variable as being defined by an immutable $ms("let")$-binding, 
  and a variable $x$ is in scope at a program point $P$, 
    if and only if its unique definition site $D_x$ strictly dominates $P$.

A given basic block can be converted to SSA form by numbering each definition of a variable,
  effectively changing references to $x$ to references to $x_t$, i.e. "$x$ at time $t$." 
For example, we could rewrite
$ x &= 3y + 5; &quad& ms("let") x_0 &= 3y + 5 \
  x &= 3x + 2; &approx& ms("let") x_1 &= 3x_0 + 2 \
  ms("ret") (3x + 1) &&&  ms("ret") (3x_1 + 1) $
This transformation enables algebraic reasoning about expressions involving each $x_t$. 
However, 
  since we can only define a variable once in SSA form, 
  expressing programs with loops and branches becomes challenging. 
For example, 
  naïvely trying to lower the program in Figure~#todo-inline[fig:fact-3addr] into SSA form would not work, 
  since the reference to $i$ in the right-hand-side of the statement $i = i + 1$ 
    can refer to _either_ the previous value of $i$ from the last iteration of the loop 
      _or_ the original value $i = 1$. 
The classical solution is to introduce _$φ$-nodes_, 
  which select a value based on the predecessor block from which control arrived. 
We give the lowering of our program into SSA with $φ$-nodes in Figure~#todo-inline[fig:fact-ssa].

@cytron-91-ssa-intro introduced the first efficient algorithm to lower a program in RTL to valid SSA 
  while introducing a minimum number of $φ$-nodes, 
  making SSA practical for widespread use as an intermediate representation. 
Unfortunately, $φ$-nodes do not have an obvious operational semantics.

Additionally, 
  they require us to adopt more complex scoping rules than simple dominance-based scoping. 
For example, 
  in the basic block $ms("loop")$ in Figure~#todo-inline[fig:fact-ssa],
  $i_0$ evaluates to 1 if we came from $ms("start")$ and to $i_1$ if we came from $ms("body")$. 
Similarly, 
  $a_0$ evaluates to either 1 or $a_1$ based on the predecessor block. 
This does not obey dominance-based scoping, 
  since $i_0$ and $i_1$ are defined _after_ the $φ$-nodes $i_0$, $a_0$ that reference them, 
    which seems counterintuitive -- after all, variables are typically used after they are defined. 
In fact, 
  since the value of a $φ$-node is determined by which basic block is our immediate predecessor, 
  we instead need to use the rule that expressions in $φ$-node branches with source $S$ 
    can use any variable $y$ defined at the _end_ of $S$. 
Note that this is a strict superset of the variables visible for a normal instruction $x$, 
  which can only use variables $y$ which _dominate_ $x$ -- i.e., 
    such that _every_ path from the entry block to the definition of $x$ goes through $y$, 
    rather than only those paths which also go through $S$.

#todo[figure: RTL vs SSA with phi-nodes]

While this rule can be quite confusing, 
  and in particular makes it non-obvious how to assign an operational semantics to $φ$-nodes, 
  the fact that the scoping for $φ$-node branches is based on the source block, 
    rather than the block in which the $φ$-node itself appears, 
  hints at a possible solution. 
By _moving_ the expression in each branch to the _call-site_, 
  we can transition to an isomorphic syntax called basic blocks with arguments (BBA), 
  as illustrated in Figure~#todo-inline[fig:fact-bba]. 
In this approach, 
  each $φ$-node -- since it lacks side effects and has scoping rules independent of its position in the basic block, 
    depending only on the source of each branch -- 
  can be moved to the top of the block. 
This reorganization allows us to treat each $φ$-node as equivalent to an argument for the basic block, 
  with the corresponding values passed at the jump site. 
Converting a program from BBA format back to standard SSA form with $φ$-nodes is straightforward: 
  introduce a $φ$-node for each argument of a basic block, 
  and for each branch corresponding to the $φ$-node, 
    add an argument to the jump instruction from the appropriate source block. 
We give a formal grammar for basic blocks-with-arguments SSA in Figure~#todo-inline[fig:bba-grammar].
#footnote[
  Many variants of SSA do not allow variables to appear alone on the right-hand side of assignments, 
    such as $x = y; β$. 
  We do not incorporate this restriction, 
    though we could by normalizing even further and substituting $[y\/x]β$ instead.
]
Note that this grammar no longer needs a separate terminator for returns: 
  we can treat the return point as a distinguished label (with argument) that a program can jump to.

#todo[figure: grammar for basic blocks-with-arguments SSA]

This allows us to use dominance-based scoping without any special cases for $φ$-nodes.
When considering basic blocks, 
  this means that a variable is visible within the block $D$ where it is defined, 
    starting from the point of its definition. 
It continues to be visible in all subsequent blocks $P$ 
  that are strictly dominated by $D$ in the control-flow graph (CFG). 
For example, in Figure~#todo-inline[fig:fact-bba]:
- $ms("start")$ strictly dominates $ms("loop")$ and $ms("body")$; 
  thus, the variable $n$ defined in $ms("start")$ is visible in $ms("loop")$ and $ms("body")$.
- $ms("loop")$ strictly dominates $ms("body")$; 
  therefore, the parameters $i_0$, $a_0$ to $ms("loop")$ are visible in $ms("body")$ 
    without the need to pass them as parameters.
- $ms("body")$ does _not_ strictly dominate $ms("loop")$, 
  since there is a path from $ms("start")$ to $ms("loop")$ that does not pass through $ms("body")$.

#todo[figure: SSA with phi-nodes vs basic-blocks with arguments]

== Type-theoretic SSA

An important insight provided by the BBA format, 
  as discussed by @appel-98-ssa and @kelsey-95-cps, 
  is that a program in SSA form can be interpreted as a collection of tail-recursive functions, 
    where each basic block and branch correspond to a function and tail call, respectively. 
This yields a natural framework for defining the semantics of SSA and reasoning about optimizations.

A program in BBA is not quite a functional program, 
  because scoping is dominance-based rather than lexically scoped. 
However, it turns out to be very easy to convert dominance-based scoping into lexical scoping. 
Observe that the function corresponding to a given basic block $B$ 
  can only be called by other blocks $B'$ having that basic block's parent $P = ms("parent")(B)$ 
    as an ancestor in the dominance tree 
      (as, otherwise, the parent would not actually dominate the block, 
        since we could get to $B$ through $B'$ without passing through $P$). 
Moreover, 
  the variables _visible_ in $B$ are exactly the variables visible at the end of $P$; 
  i.e., the variables visible in $P$ and those defined in $P$.

So if we make the dominance tree explicit in the syntax and tie the binding of variables to this tree structure, 
  then lexical and dominance-based scoping become one and the same. 
We use this observation to introduce _lexical SSA_ in Figure~#todo-inline[fig:lex-ssa]. 
The key idea of this syntax is to, 
  rather than treating the control-flow graph $G$ as a flat collection of basic blocks 
    (with a distinguished block), 
  to instead consider (subtrees of) the dominance tree $r$, 
    with the root of the tree implicitly being the entry block. 
We call such subtrees _regions_: 
  we note that they have a single entry (the root) and multiple exits (the leaves), 
  and so generalize the more standard concept of a single-entry-single-exit region in a CFG.

In particular, 
  a _region_ $r$ generalizes a basic block $β$ by annotating the terminator $τ$ 
    with a list $L$ of _labeled branches_ "$wbranch(ℓ_i, x_i, t_i)$," 
  yielding a _$ms("where")$-block_ "$where(τ, L)$." 
Each $ℓ_i$ can only be branched to by $τ$ and the regions $t_i$, 
  thus syntactically enforcing that the basic block at the root of $r$ 
    (made up of its instructions and terminators) 
  _dominates_ all the basic blocks in the subregions $t_i$ 
    (which can only be reached through $r$). 
The data of a region $r$ is thus exactly the data contained in a basic block $β$ 
  (its instructions and terminator) 
  together with a set of subregions dominated by $r$; 
  in C++-like pseudocode, we might represent a region as in Figure~#todo-inline[fig:ssa-data].

Regions allow us to enforce dominance-based scoping simply by making the variables defined in $r$ 
  visible only in the $t_i$, 
  which, as previously stated, _must_ be dominated by $r$; 
  i.e., dominance based scoping becomes lexical scoping of $ms("where")$-blocks. 
It is easy to see 
  (we demonstrate this more rigorously in Section~#todo-inline[ssec:ssa-normal]) 
  that, given a CFG $G$, 
    there exists some way to annotate its topological sort w.r.t. the dominance relation 
      with $ms("where")$-blocks 
    to obtain a region $r$ which is lexically well-scoped 
      if and only if $C$ is a valid SSA program; 
we illustrate this process on our running example in Figure~#todo-inline[fig:dominance-to-lexical]. 
Conversely, 
  erasing the $ms("where")$-blocks from a region $r$ and giving the root a name 
    trivially yields a (topologically sorted!) SSA program, 
  establishing an isomorphism between lexical SSA and standard SSA.

#todo[figure: grammar for lexically-scoped SSA]

#todo[figure: data encoded by the grammar (C++ code)]

#todo[figure: conversion from dominance-based scoping to explicit lexical scoping]

Lexical scoping allows us to apply many of techniques developed in type theory and functional programming 
  for reasoning about program transformations. 
Indeed, 
  the result of our conversion to lexical scoping looks a lot like the correspondence 
    between SSA and CPS described in @kelsey-95-cps. 
We can use this correspondence to guide us in developing an _equational theory_ for SSA programs, 
  with the goal of enabling compositional reasoning about program transformations such as:
- _Control-flow rewrites_, 
  such as jump-threading or fusing two identical branches of an $ms("if")$-statement
- _Algebraic rewrites_, 
  such as simplifying arithmetic expressions
- Combinations of the two, 
  such as rewriting "$ms("if") x > 0 thick ms("then") 0 - x thick ms("else") x$" to "$ms("abs")(x)$".
  #todo[use the same syntax for ITE everywhere?]

To help achieve this, we will slightly generalize our syntax by:
+ Fusing the syntactic categories $o, v$ of operations and values 
  into the syntactic category $a$ of _expressions_ <ssa-change-val>
+ Fusing the syntactic category $τ$ of terminators 
  into the syntactic category of regions $r$. <ssa-change-reg>
+ Extending expressions $a$ to allow _let-expressions_ "$letexpr(x, a, b)$" 
  and _case-expressions_ "$caseexpr2(a, x, b, y, c)$" <ssa-change-expr>

This leaves us with our final language, #todo-inline[isotopessa], 
  the resulting grammar for which is given in Figure~#todo-inline[fig:ssa-grammar]. 
It is easy to see that these changes add no expressive power to lexical SSA: 
  we can desugar (1) by introducing names for anonymous sub-expressions, 
  (2) by introducing names for anonymous sub-regions, 
  and (3) by floating out let-bindings and case-statements in the obvious manner, 
    introducing labels as necessary; 
  we discuss this in more detail in Section~#todo-inline[ssec:ssa-normal].

Change (1) allows us to effectively reason about _substitution_: 
  replacing the value of a variable (which is a value $v$) 
    with its definition (which is an instruction $o$). 
This can be used as a building block for optimizations 
  such as common subexpression elimination and global value numbering; 
  combined with change (3), 
    we can also reason algebraically about "branching" operations 
      like conditional move and absolute value.

On the other hand, 
  (2) lets us replace an unconditional branch $brb(ℓ, a)$ 
    (which is a terminator $τ$) 
  with the code _pointed to_ by the label $ℓ$ (which is a region $r$), 
  allowing us to perform the jump-threading optimization
$ where(letstmt(x, a, brb(ℓ, b)), wbranch(ℓ, y, r))
  equiv where(letstmt(x, a, letstmt(y, b, r)), wbranch(ℓ, y, r)) $
While both sides of this equation are valid lexical SSA programs, 
  by loosening our syntax slightly, 
  we can _unconditionally_ replace jumps with regions, 
    without worrying about jumps nested in case statements or fusing $ms("where")$-blocks. 
This, especially combined with change (3), 
  makes it much easier to verify optimizations such as
$ & where(casestmt2(a, x, brb(ℓ, (ι_r x)), x, brb(ℓ, (ι_l x))),
      wbranch(ℓ, y, casestmt2(y, z, ms("ret") (ι_r z), z, ms("ret") (ι_l z)))) \
  &equiv casestmt2(a, 
    x, casestmt2(ι_r x, z, ms("ret") (ι_r z), z, ms("ret") (ι_l z)), \
    & #h(2em) x, casestmt2(ι_l x, z, ms("ret") (ι_r z), z, ms("ret") (ι_l z))) \
  &equiv casestmt2(a,
    x, ms("ret")(ι_l x),
    x, ms("ret")(ι_r x))
  equiv ms("ret") (casestmt2(a, x, ι_l x, x, ι_r x))
  equiv ms("ret") a $
by repeatedly applying a set of known-good rules, 
  and, moreover, dramatically simplifies the form of the rules themselves.

#todo[figure: grammar for isotopessa]

= Refinement

#todo[TOPLAS + refinement here]

= Lowering to SSA

#todo[λiter ↔ Type Theoretic SSA]

#todo[Type Theoretic SSA ⊇ ANF]

#todo[ANF ⊇ Lexical SSA]

#todo[⇒ λiter ↔ Lexical SSA]

#todo[Lexical SSA ↔ Graph SSA]

= Denotational Semantics of SSA

#todo[TOPLAS + refinement here]

= Simple Models of SSA

#todo[Partiality]

#todo[Nondeterminism]

#todo[Elgot monad transformers]

#todo[Heaps and printing]

= Verified Optimizations

#todo[the basics: CSE, GVN, DCE, SCCP, peephole @siddharth-24-peephole]

#todo[E-graphs @cranelift]

#todo[Vectorization]

#todo[`mem2reg`]

= Memory Models for SSA

== Brookes Models

#todo[Brookes-style @brookes-96-sc-abstract concurrency models]

== Interaction Trees and Choice Trees

#todo[ITrees @xia-20-itrees and CTrees @chappe-25-ctrees]

== Trace Models

#todo[Stream actions, pomsets, and TSO]

= Future Work

#todo[literally an infinite pile]

#bibliography("refs.bib")
