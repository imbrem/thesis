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
#let letstmt(x, a, t) = $ms("let") #x = #a seq #t$
#let letexpr(x, a, e) = $ms("let") #x = #a seq #e$
#let bhyp(x, A, q: []) = $#x : #A^#q$
#let lhyp(ℓ, A) = $#ℓ (#A)$
#let hasty(Γ, ε, a, A) = $#Γ ⊢_#ε #a : #A$
#let haslb(Γ, r, L) = $#Γ ⊢ #r triangle.stroked.small.r #L$
#let issubst(γ, Γ, Δ) = $#γ : #Γ => #Δ$
#let lbsubst(Γ, σ, L, K) = $#Γ ⊢ #σ : #L arrow.r.long.squiggly #K$
#let isop(f, A, B, ε) = $#f : #A ->^#ε #B$
#let tmeq(Γ, ε, a, b, A) = $#Γ ⊢_#ε #a equiv #b : #A$
#let lupg(γ) = $upright(↑)#γ$
#let rupg(γ) = $#γ upright(↑)$

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
#align(center, stack(dir: ltr, spacing: 3em,
  $ & x = 3y + 5 ; \ & x = 3x + 2; \ & retb((3x + 1))$,
  align(horizon, $≈$),
  $ & x_0 = 3y + 5 ; \ & x_1 = 3x_0 + 2 ; \ & retb((3x_1 + 1))$
))
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
#todo[clean up optimization here]
$ 
  & where(casestmt2(a, x, brb(ℓ, (ι_r x)), x, brb(ℓ, (ι_l x))),
      wbranch(ℓ, y, casestmt2(y, z, ms("ret") (ι_r z), z, ms("ret") (ι_l z)))) \
  &equiv casestmt2(a, 
    x, casestmt2(ι_r x, z, ms("ret") (ι_r z), z, ms("ret") (ι_l z)), \
    & #h(2em) x, casestmt2(ι_l x, z, ms("ret") (ι_r z), z, ms("ret") (ι_l z))) \
  &equiv casestmt2(a,
    x, ms("ret")(ι_l x),
    x, ms("ret")(ι_r x))
  equiv ms("ret") (casestmt2(a, x, ι_l x, x, ι_r x))
  equiv ms("ret") a 
$
by repeatedly applying a set of known-good rules, 
  and, moreover, dramatically simplifies the form of the rules themselves.

#todo[figure: grammar for isotopessa]

= Type Theory

#todo[fuse with refined account of SSA]

We now give a formal account of #todo-inline[isotopessa], starting with the types. 
Our types are first order, 
  and consists of binary sums $A + B$, products $A times.o B$, the unit type $mb(1)$, 
  and the empty type $mb(0)$, 
  all parameterised over a set of base types $X in cal(T)$. 
We write our set of types as $ms("Ty")(X)$.

A (variable) _context_ $Γ$ is a list of _typing hypotheses_ $bhyp(x, A)$, 
  where $x$ is a variable name and $A$ is the type of that variable. 
Similarly, 
  we define a _label-context_ to be a list of _labels_ $lhyp(ℓ, A)$, 
  where $A$ is the parameter type that must be passed on a jump to the label $ℓ$. 
The grammar for types, contexts, and label-contexts is given in Figure~#todo-inline[fig:ssa-types].

#todo[figure: grammar for isotopessa types, contexts, and label-contexts]

Our grammar in Figure~#todo-inline[fig:ssa-grammar] was implicitly parameterised over a set of 
  _primitive instructions_ $f in cal(I)$. 
In particular, 
  for each pair $A, B in ms("Ty")(X)$ we specify a set of primitive instructions $f in cal(I)(A, B)$, 
  with a subset of _pure instructions_ $cal(I)_bot (A, B)$. 
To allow us to write $cal(I)_ε$ for an _effect_ $ε in {top, bot}$, 
  we denote $cal(I)_top (A, B) := cal(I)(A, B)$. 
In general, we define $cal(I)_ε = union.big_(A, B) cal(I)_ε (A, B)$, 
  and $cal(I) = union.big_ε cal(I)_ε$.

We'll call a tuple $S g = (cal(T), cal(I))$ of types and instructions over these types 
  an _#todo-inline[isotopessa]-signature_, 
  and, for the rest of this section, work over a fixed signature.

#todo[change to definition list]

As shown in Figure~#todo-inline[fig:ssa-grammar], 
  #todo-inline[isotopessa] terms are divided into two syntactic categories, 
  each associated with a judgement:
- _Expressions_ $a, b, c, e$, 
  which are typed with the judgement $hasty(Γ, ε, a, A)$, 
  which says that under the typing context $Γ$, 
    the expression $a$ has type $A$ and effect $ε$. 
  We say a term is _pure_ if it has effect $bot$; 
  note that whether an expression is pure or not depends both on the expression itself 
    and on the purity of the variables used in the expression; 
  this is to allow reasoning about impure substitutions.
- _Regions_ $r, s, t$, 
  which recursively define a lexically-scoped SSA program with a single entry 
    and (potentially) multiple exits. 
  This is typed with the judgement $haslb(Γ, r, ms("L"))$, 
  which states that given that $Γ$ is live at the unique entry point, 
    $r$ will either loop forever or branch to one of the exit labels in $ℓ(A) in ms("L")$ 
      with an argument of type $A$.

The typing rules for expressions are given in Figure~#todo-inline[fig:ssa-expr-rules]. 
In particular, expressions may be built up from the following fairly standard primitives:
- A variable $x$ in the context $Γ$, as typed by #todo-inline[rle:var].
- A _primitive instruction_ $f in cal(I)_ε (A, B)$ applied to an expression $hasty(Γ, ε, a, A)$, 
  typed by #todo-inline[rle:op]
- Unary and binary _let-bindings_, 
  typed by #todo-inline[rle:let₁] and #todo-inline[rle:let₂] respectively
- A _pair_ of expressions $hasty(Γ, ε, a, A)$, $hasty(Γ, ε, b, B)$, 
  typed by #todo-inline[rle:pair]. 
  Operationally, we interpret this as executing $a$, and then $b$, 
    and returning the pair of their values.
- An empty tuple $()$, which types in any context by #todo-inline[rle:unit]
- Injections, typed by #todo-inline[rle:inl] and #todo-inline[rle:inr]
- Pattern matching on sum types, typed by #todo-inline[rle:case]. 
  Operationally, we interpret this as executing $e$, 
    and then, if $e$ is a left injection $ι_l x$, executing $a$ with its value ($x$), 
    otherwise executing $b$.
- An operator $ms("abort") e$ allowing us to abort execution if given a value of the empty type. 
  Since the empty type is a 0-ary sum type, 
    $ms("abort")$ can be seen as a $ms("case")$ with no branches. 
  Since the empty type is uninhabited, execution can never reach an $ms("abort")$. 
  This can be viewed as a typesafe version of the `unreachable` instruction in LLVM IR.

Traditional presentations of SSA use a boolean type instead of sum types. 
Naturally, booleans can be encoded with sum types as $mb(1) + mb(1)$. 
If-then-else is then a $ms("case")$ which ignores the unit payloads, 
  so that $ite(e_1, e_2, e_3) := caseexpr2(e_1, (), e_2, (), e_3)$.

#todo[figure: rules for typing isotopessa expressions]

We now move on to _regions_, which can be typed as follows:
- A branch to a label $ℓ$ with pure argument $a$, typed with #todo-inline[rle:br].
- Unary and binary _let-bindings_, 
  typed by #todo-inline[rle:let₁-r] and #todo-inline[rle:let₂-r] respectively
- Pattern matching on sum types, typed by #todo-inline[rle:case-r]. 
  Operationally, we interpret this as executing the expression $e$, 
    and then, if $e$ is a left injection $ι_l x$, executing $r$ with its value ($x$), 
    otherwise executing $s$.
- _$ms("where")$-blocks_ of the form "$where(r, (wbranch(ℓ_i, x_i, t_i))_i)$", 
  which consist of a collection of mutually recursive regions $wbranch(ℓ_i, x_i, t_i)$ 
    and a _terminator region_ $r$ which may branch to one of $ℓ_i$ or an exit label.

#todo[figure: rules for typing isotopessa regions]

== Metatheory

We can now begin to state the syntactic metatheory of #todo-inline[isotopessa]. 
One of the most important metatheorems, 
  and a basic sanity check of our type theory, 
  is _weakening_; 
  essentially, if something typechecks in a context $Δ$, 
    and $Γ$ contains all the variables of $Δ$ 
      (written $Γ ≤ Δ$, pronounced "$Γ$ _weakens_ $Δ$"), 
  then it should typecheck in the context $Γ$ as well. 
Here, the context with fewer variables appears on the _right_, 
  allowing us to compose typing judgements likeso
$ Γ ≤ Δ ==> haslb(Δ, r, ms("L")) ==> haslb(Γ, r, ms("L")) $
As our theory has two types of context; 
  we'd also like to define _label-weakening_ $ms("L") ≤ ms("K")$, 
  which we should be able to apply in the same manner:
$ haslb(Γ, r, ms("L")) ==> ms("L") ≤ ms("K") ==> haslb(Γ, r, ms("K")) $
If a region $r$ typechecks with exit labels $ms("L")$, 
  and $ms("K")$ contains every label in $ms("L")$, 
  then $r$ should obviously also typecheck in $ms("K")$. 
It follows that in the judgement $ms("L") ≤ ms("K")$ 
  the context with fewer labels appears on the _left_-hand side of the judgement: 
  this corresponds precisely to the fact that label-weakening (injection into a coproduct) 
    is semantically dual to variable-weakening (projection from a product), 
  and hence the order is flipped.

We give the (standard) formal rules for weakening $Γ ≤ Δ$, and their duals, 
  in the first part of Figure~#todo-inline[fig:ssa-meta-rules].
- #todo-inline[rle:wk-nil] and #todo-inline[rle:lwk-nil] say that the empty (label) context weakens itself,
- #todo-inline[rle:wk-skip] says that if $Γ$ weakens $Δ$, 
  then $Γ, bhyp(x, A)$ also weakens $Δ$ for arbitrary (fresh) $x$. 
  Dually, #todo-inline[rle:lwk-skip] says that if $ms("L")$ weakens $ms("K")$, 
    then $ms("L")$ also weakens $ms("K"), lhyp(ℓ, A)$ for arbitrary (fresh) $ℓ$.
- #todo-inline[rle:wk-cons] says that if $Γ$ weakens $Δ$, 
  then $Γ$ with $bhyp(x, A)$ added weakens $Δ, bhyp(x, A)$. 
  Likewise, #todo-inline[rle:lwk-cons] says that if $ms("L")$ weakens $ms("K")$, 
    then $ms("L")$ with $lhyp(ℓ, A)$ added weakens $ms("K"), lhyp(ℓ, A)$.

It is easy to see that (label) weakening defined in this manner induces a partial order on (label) contexts. 
Our weakening lemma is then as follows:

#todo[proper lemma; proof from a package]

#let lemma(title, body) = block[
  *Lemma* (#title). #body
]

#lemma[Weakening][
  Given $Γ ≤ Δ$, $ε ≤ ε'$, we have that:
  + If $hasty(Δ, ε, a, A)$, then $hasty(Γ, ε', a, A)$
  + If $ms("L") ≤ ms("K")$ and $haslb(Δ, r, ms("L"))$, then $haslb(Γ, r, ms("K"))$
  + If $issubst(γ, Δ, Ξ)$, then $issubst(γ, Γ, Ξ)$
  + If $lbsubst(Δ, σ, ms("L"), ms("K"))$, then $lbsubst(Γ, σ, ms("L"), ms("K"))$
]

#let proof(body) = block[
  _Proof._ #body #h(1fr) $qed$
]

#proof[
  These are formalized as:
  + `Term.Wf.wk` in `Typing/Term/Basic.lean`
  + `Region.Wf.wk` in `Typing/Region/Basic.lean`
  + Follows from `Term.Subst.Wf.comp` in `Typing/Term/Subst.lean`
  + Follows from `Region.Subst.Wf.vsubst` in `Typing/Region/LSubst.lean`
]

#todo[figure: rules for typing isotopessa weakening and substitution]

The validity of variable weakening hinges on the fact that all the variables in $Δ$ 
  are also available with the same type in $Γ$, 
  i.e., if $hasty(Δ, ε, x, A) ==> hasty(Γ, ε, x, A)$, 
    then anything which can be typed in $Δ$ can be typed in $Γ$. 
So while weakening on _terms_ is just the identity, 
  weakening on _derivations_ is essentially replacing "variables from $Δ$" with "variables from $Γ$." 
Since none of our typing rules, other than $ms("var")$, make use of variable names, 
  we might ask whether we can repeat essentially the same reasoning to reason about the well-typedness 
    of replacing variables in $Γ$ with arbitrary pure expressions of the same type 
      (i.e., perform a substitution).

An assignment of such variables $γ : x |-> γ_x$ is called a _substitution_, 
  which we can type with the judgement $issubst(γ, Γ, Δ)$ 
    as per the rules given in Figure~#todo-inline[fig:ssa-meta-rules]. 
In particular,
- #todo-inline[rle:sb-nil] says that the empty substitution takes every context to the empty context.
- #todo-inline[rle:sb-cons] says that if $γ$ takes $Γ$ to $Δ$ and $hasty(Γ, bot, e, A)$, 
  then $γ$ with the additional substitution $x |-> e$ adjoined takes $Γ$ to $Δ, bhyp(x, A)$

To _use_ a substitution, we simply need to perform standard capture-avoiding substitution 
  (see Figure~#todo-inline[fig:ssa-subst-def] in the appendix). 
Substitution satisfies the _substitution lemma_ as follows:

#lemma[Substitution][
  Given $issubst(γ, Γ, Δ)$, we have that:
  + $hasty(Δ, ε, a, A) ==> hasty(Γ, ε, [γ]a, A)$
  + $haslb(Δ, r, ms("L")) ==> haslb(Γ, [γ]r, ms("L"))$
  + $issubst(γ_2, Δ, Ξ) ==> issubst([γ]γ_2, Γ, Ξ)$
  + $lbsubst(σ, Γ, ms("L"), ms("K")) ==> lbsubst([γ]σ, Δ, ms("L"), ms("K"))$
]

#proof[
  These are formalized as:
  + `Term.Wf.subst` in `Typing/Term/Subst.lean`
  + `Region.Wf.vsubst` in `Typing/Region/VSubst.lean`
  + `Term.Subst.Wf.comp` in `Typing/Term/Subst.lean`
  + `Region.Subst.Wf.vsubst` in `Typing/Region/LSubst.lean`
]

Note in particular that this allows us to take the _composition_ 
  $issubst([γ']γ, Γ', Δ)$ of substitutions $issubst(γ', Γ', Γ)$ and $issubst(γ, Γ, Δ)$; 
  the composition associates as expected: 
    $[[γ_1]γ_2]γ_3 = [γ_1]([γ_2]γ_3)$, 
  and has identity $[ms("id")]γ = γ$, 
  yielding a category of substitutions with variable contexts $Γ$ as objects.

Given a substitution $issubst(γ, Γ, Δ)$ and context $Ξ$ disjoint from $Γ$ and $Δ$, 
  we may define a "left extension" operation $lupg(dot.c)_Ξ$ 
    yielding $issubst(lupg(γ)_Ξ, Ξ\, Γ, Ξ\, Δ)$ 
  which appends the identity substitution for each variable in $Ξ$ in the obvious manner:
$ lupg(γ)_(dot.c) = γ quad lupg(γ)_(Ξ, bhyp(x, A)) = x |-> x, lupg(γ)_Ξ $
We may similarly define a "right extension" operation $rupg(dot.c)_Ξ$ 
  yielding $issubst(rupg(γ)_Ξ, Γ\, Ξ, Δ\, Ξ)$ as follows:
$ rupg(γ)_(dot.c) = γ quad rupg(γ)_(Ξ, bhyp(x, A)) = rupg(γ)_Ξ, x |-> x $
In particular, we note that the identity substitution on $Γ$ can be written as $rupg(dot.c)_Γ$; 
  in general, we have $[γ]a = [lupg(Γ)_Ξ]a = [rupg(γ)_Ξ]a$. 
We will usually infer $Ξ$ from context.

One other particularly important form of substitution is that of substituting an expression $a$ 
  for an individual variable $x$, 
  which we will write $[a\/x] := lupg((x |-> a))$.

Finally, just as we can generalize weakening by substituting expressions for variables via substitution, 
  we can generalize label weakening by substituting _labels_ for _(parametrized) regions_ 
    via _label substitution_. 
In particular, 
  a label-substitution $lbsubst(Γ, σ, ms("L"), ms("K"))$ 
    maps every label $ℓ(A) in ms("L")$ to a region $haslb((Γ, bhyp(x, A)), r, ms("K"))$ 
      parametrized by $bhyp(x, A)$. 
As shown in Figure~#todo-inline[fig:ssa-label-subst-def], 
  we may then define label-substitution recursively in the obvious manner, 
  mapping $brb(ℓ, a)$ to $[a\/x]r$ as a base case. 
Composition of label-substitutions is pointwise. 
This allows us to state _label substitution_ as follows:

#lemma[Label substitution][
  Given $lbsubst(Γ, σ, ms("L"), ms("K"))$, we have that
  + $haslb(Γ, r, ms("L")) ==> haslb(Γ, [σ]r, ms("K"))$
  + $lbsubst(Γ, κ, ms("L"), ms("J")) ==> lbsubst(Γ, [σ]κ, ms("K"), ms("J"))$
]

#proof[
  These are formalized as:
  + `Region.Wf.lsubst` in `Typing/Region/LSubst.lean`
  + `Region.Subst.Wf.comp` in `Typing/Region/LSubst.lean`
]

We may similarly define left and right extensions 
  $lbsubst(Γ, lupg(σ)_(ms("K")), ms("L")\, ms("J"), ms("K")\, ms("J"))$ 
  and $lbsubst(Γ, rupg(σ)_(ms("K")), ms("L")\, ms("J"), ms("K")\, ms("J"))$ 
  for label substitutions $lbsubst(Γ, σ, ms("L"), ms("K"))$ in the obvious manner:
$ rupg(σ)_(dot.c) &= σ quad rupg(σ)_(ms("K"), ℓ(A)) &= rupg(σ)_(ms("K")), ℓ(x) |-> brb(ℓ, x) \
  lupg(σ)_(dot.c) &= σ quad lupg(σ)_(ms("K"), ℓ(A)) &= ℓ(x) |-> brb(ℓ, x), lupg(σ)_(ms("K")) $
As for variable substitutions, we will often omit $ms("L")$ when it is clear from the context.
We also define the shorthand $[ℓ \/ κ] = [lupg((κ(x) |-> brb(ℓ, x)))]$ for single-label substitutions.

#todo[figure: capture-avoiding label substitution for isotopessa regions and label substitutions]

= Equational Theory

== Expressions

We can now give an equational theory for #ms()[IsotopeSSA] expressions. In particular, we will
inductively define an equivalence relation
$
tmeq(Gamma, epsilon, a, a', A)
$
on terms $a, a'$ for each context $Gamma$, effect $epsilon$, and type $A$. For each of the rules
we will present, we assume the rule is valid if and only if _both sides_ of the rule are
well-typed. We also assume that variables are $alpha$-converted as appropriate to avoid shadowing;
our formalization uses de Bruijn indices, but we stick with names in this exposition for simplicity.

The rules for this relation can be roughly split into _rewriting rules_, which denote when two
particular expressions have equivalent semantics, and _congruence rules_, which govern how
rewrites can be composed to enable equational reasoning. In particular, our congruence rules, given
in #todo[Figure: fig:ssa-expr-congr-rules], consist of:
- #todo-inline[refl], #todo-inline[symm], #todo-inline[trans], which state that
  $tmeq(Gamma, epsilon, dot, dot, A)$ is reflexive, transitive, and symmetric respectively
  for each choice of $Gamma, epsilon, A$, and therefore an equivalence relation.
- #todo-inline[let₁], #todo-inline[let₂], #todo-inline[pair], #todo-inline[inl], #todo-inline[inr], #todo-inline[case], and
  #todo-inline[abort], which state that $tmeq(Gamma, epsilon, dot, dot, A)$ is a _congruence_
  with respect to the corresponding expression constructor, and, in particular, that the expression
  constructors are well-defined functions on the quotient of expressions up to $equiv$.

We also include the following _type-directed_ rules as part of our congruence relation:
- #todo-inline[initial], which equates _all_ terms in a context containing the empty type
  $mb(0)$, since we will deem any such context to be _unreachable_ by control flow. In
  particular, any instruction or function call returning $mb(0)$ is assumed to diverge. 
- #todo-inline[terminal], which equates all _pure_ terms of unit type $mb(1)$. Note that
  _impure_ terms may be disequal, since while their result values are the same, their side
  effects may differ!

#todo[Figure: Congruence rules for #ms()[IsotopeSSA] expressions.
Rules: refl, trans, symm, let₁, pair, let₂, inl, inr, case, abort, initial, terminal]

We may group the rest of our rules according to the relevant constructor, i.e. #ms()[let] (unary and
binary) and #ms()[case]. In particular, for unary #ms()[let], we have the following rules,
summarized in #todo[Figure: fig:ssa-unary-let-expr]:
- #todo-inline[let₁-β], which allows us to substitute the bound variable in $x$ the
  let-statement $letexpr(x, a, b)$ with its definition $a$, yielding $[a slash x]b$. Note that we require
  $hasty(Gamma, bot, a, A)$; i.e., $a$ must be _pure_.

- #todo-inline[let₁-η], which is the standard $eta$-rule for #ms()[let]. This is included as a
  separate rule since, while it follows trivially from $beta$ for pure $a$, we also want to
  consider _impure_ expressions.
  
- Rules #todo-inline[let₁-op], #todo-inline[let₁-let₁], #todo-inline[let₁-let₂],
  #todo-inline[let₁-abort], and #todo-inline[let₁-case] which allow us to "pull" a let-statement out of
  any of the other expression constructors; operationally, this is saying that the bound expression
  we pull out is evaluated before the rest of the #ms()[let]-binding.
  
  For example, #todo-inline[let₁-case] says that, if both
  $letexpr(z, casestmt2(e, x, a, y, b), d)$ and
  $casestmt2(e, x, letexpr(z, a, d), y, letexpr(z, b, d))$,
  are well typed, then both must have the same behaviour:
  + Compute $e$
  + If $e = linl(e_l)$, compute $[e_l slash x]a$, else, if $e = linr(e_r)$, compute $[e_r slash y]b$;
    store this value as $z$
  + Compute $d$ given our value for $z$
  Note in particular that, since both sides are well-typed, $d$ cannot depend on either $x$ or $y$.

#todo[Figure: Rewriting rules for #ms()[IsotopeSSA] unary #ms()[let] expressions.
Rules: let₁-β, let₁-η, let₁-op, let₁-let₁, let₁-let₂, let₁-abort, let₁-case]

Handling the other type constructors is a little simpler: by providing a "binding" rule, we
generally only need to specify how to interact with $ms("let")_1$, as well as an $eta$ and $beta$
rule; interactions with the other constructors can then be derived. For example, consider the rules
for $ms("let")_2$ given in #todo-inline[fig:ssa-let2-case-expr]; we have:
- #todo-inline[let₂-η], which is the standard $eta$-rule for binary #ms()[let]-bindings
- #todo-inline[let₂-pair], which acts like a slightly generalized $beta$-rule, since we can
  derive $beta$ reduction as follows: given pure $hasty(Gamma, bot, a, A)$ and
  $hasty(Gamma, bot, b, B)$, we have
  $
  (letexpr((x, y), (a, b), c)) 
  equiv (letexpr(x, a, letexpr(y, b, c)))
  equiv ([a slash x](letexpr(y, b, c)))
  equiv ([a slash x][b slash y]c)
  $
  We state the rule in a more general form to allow for impure $a$ and $b$, as well as to simplify
  certain proofs.
- #todo-inline[let₂-bind], which allows us to "pull" out the bound value of a binary
  #ms()[let]-expression into its own unary #ms()[let]-expression; operationally, this just says that
  we execute the bound value before executing the binding itself.

This is enough to allow us to define our interactions with the other expression constructors: for
example, to show that we can lift an operation $f$ out of a binary #ms()[let]-binding, rather than
adding a separate rule, we can instead derive (types omitted for simplicity) it from
#todo-inline[let₂-bind] and #todo-inline[let₁-op] as follows:
$
(letexpr((x, y), f space a, b))
&equiv (letexpr(z_f, f space a, letexpr((x, y), z, b))) \
&equiv (letexpr(z_a, a, letexpr(z_f, f space z_a, letexpr((x, y), z, b)))) \
&equiv (letexpr(z_a, a, letexpr((x, y), f space z_a, b)))
$

#todo[Figure: Rewriting rules for #ms()[IsotopeSSA] binary #ms()[let] and #ms()[case] expressions.
Rules: let₂-pair, let₂-η, let₂-bind, case-inl, case-inr, case-η, case-bind]

Similarly, it is enough to give $eta$, $beta$, and binding rules for #todo-inline[case] expressions. 
In particular, we have that
- #todo-inline[case-inl] and #todo-inline[case-inr] serve as $beta$-reduction rules, telling us that
  #ms()[case]-expressions given an injection as an argument have the expected operational behaviour.
  Note that we reduce to a #ms()[let]-expression rather than perform a substitution to allow for
  impure discriminants.
- #todo-inline[case-η] is the standard $eta$-rule for #ms()[case]-expressions.
- #todo-inline[case-bind] allows us to "pull" out the bound value of the discriminant into
  it's own #ms()[let]-expression; again, operationally, this just says that we need to evaluate
  the discriminant before executing the #ms()[case]-expression.

It's interesting that this is enough, along with the #todo-inline[let-case] rule and friends, to derive the
distributivity properties we would expect well-behaved #ms()[case]-expressions to have. For example,
we have that
$
f(casestmt2(e, x, a, y, b)) 
&equiv (letexpr(z, casestmt2(e, x, a, y, b), f space z)) \
&equiv casestmt2(e, x, letexpr(z, a, f space z), y, letexpr(z, b, f space z)) \
&equiv casestmt2(e, x, f space a, y, f space b)
$
and likewise for more complicated distributivity properties involving, e.g., #ms()[let]-bindings.

The case for the other constructors is even more convenient: no additional rules are required
at all to handle operations, pairs, and injections. For example, we can derive the expected
bind-rule for operations as follows:
$
f space a equiv (letexpr(y, f space a, y))
equiv (letexpr(x, a, letexpr(y, f space x, y)))
equiv (letexpr(x, a, f space x))
$

This completes the equational theory for #ms()[IsotopeSSA] terms; in #todo-inline[Section: ssec:completeness], we
will show that this is enough to state a completeness theorem.

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

#todo[E-graphs @cranelift; see also Peggy]

#todo[Vectorization]

#todo[`mem2reg`]

= Memory Models for SSA

== Brookes Models

#todo[Brookes-style @brookes-96-sc-abstract concurrency models]

== Interaction Trees and Choice Trees

#todo[ITrees @xia-20-itrees and CTrees @chappe-25-ctrees]

== Trace Models

#todo[Stream actions, pomsets, and TSO]

= Formalization of SSA

#todo[link down here for type theory discussion, once we've moved to refined account]

== `discretion`

#todo[describe discretion library; premonoidal port]

== `debruijn-ssa`

#todo[describe debruijn-ssa library]

== `refined-ssa`

#todo[describe refined-ssa library]

== `ln-ssa`

#todo[describe ln-ssa library, if we've got anything by the end...]

= Future Work

#todo[literally an infinite pile]

#bibliography("refs.bib")
