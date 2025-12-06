#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/simplebnf:0.1.1": *
#import "@preview/subpar:0.2.2"

#import "@preview/wordometer:0.1.5": word-count
#show: word-count.with(exclude: <no-wc>)

#let production = false;

#import "thesis-template.typ": *
#import "todos.typ": todo, todo-inline, total-todos, stats-box

#import "syntax.typ": *

#set text(lang: "en")

#set heading(numbering: "1.")

#let scaffold(content) = [
  #content
]

#let notes(content) = [
  #content <no-wc>
]

#set document(
  title: [Categorical imperative programming: type theory, refinement, and semantics for SSA],
  author: "Jad-Elkhaleq Ghalayini",
  date: datetime(day: 12, month: 1, year: 2026),
)

#align(center + horizon)[
  #title()

  #context document.author.at(0)

  \

  \

  #context document.date.display("[month repr:long] [year]")

  \

  \


  #image("ucam-cs-colour.svg", width: 15em)

  \

  \

  \

  #stats-box(production)
]

#pagebreak()

#statement-of-originality

#todo[

  We should factor this template, and have a global TODOs list, maybe outside the document...

  What's the right way to format this?

  Do we put the acknowledgements here or after the abstract?

]

#todo[go make a proper listing function for code...]

#todo[go follow the outline I came up with with Neel...]

#pagebreak()

#align(center + horizon)[
  Is _this_ abstract enough?
  #todo[Actually write an abstract]
]

#pagebreak()

#outline()

#pagebreak()

= Introduction

#todo[
  TFW I need a thesis statement
]

#todo[
  High level:
  - Step 1: we want an MVP thesis, which is:
    - The type theory of TOPLAS, but refined and with λiter
      - Sandwich:
        - Introduction:
          - Buildup RTL => SSA => LexSSA in language to go from states to variables
          - Buildup LexSSA ⊆ LexSSA ExpTree [mention Cranelift as prior art]
                           ⊆ LexSSA CaseExpTree [conditional moves, don't introduce big branches]
                           ⊆ LexSSA λiter [natural generalization, mention ML, Peggy, and RVSDG as prior art]
          - Buildup LexSSA λiter ⊆ TTSSA λiter
          - Expressions first (as classical), control later (as this is us, but prior art too see Peggy)
          - Power is the same, and since ⊆ rather than $=>$ type theory for top level gives us type theory for everything else
            - (But, not a type theory for RTL and SSA; see MVP₃)
        - Body:
          - Chapter 1: TT following POPL; _no quantities_, _no effects_
            - TT for λiter
              - NO talk about quantities; DO LATER
              - NO _extended_ talk about effects; DO LATER
              - But do note, when stating substitution theorem, that just because the term _makes sense_ doesn't mean the substitution is _valid_
              - Unlike POPL instead of coproducts we have enums. This will be more familiar to complier folks, but we need to discuss how booleans and coproducts are just a special case.
            - TT for λSSA (parametric over expression language instantiate for λiter)
              - Talk about labels
              - This is a lot easier than before, since instead of coproducts we have enums. So a label is a glorified enum. 
            - Pure syntatic metatheory of:
              - Substitution
              - Label-substitution
          - Chapter 2: 
            - Expo:
              - Motivate refinement by means of effects as below
              - Introduce λiter type theory with effects parametrized by primitive effects on terms
              - Motivate usage tracking by means of _advanced_ refinements
                - `unspec` would always need to be a refinement without usage tracking
                - but _with_ usage tracking, linear use is not a refinement!
              - Introduce λiter type theory with _only_ usage tracking

              - Observation:
                - λiter with effects is trivial, λssa with effects is trivial
                - λiter with usage introduces a complex concept: _splitting_


            - Pure and impure `let x = read(); (x, x) ≠ (read(), read())`
            - But, _refinement_ (point to probabilistic programming and friends)

              `let x = unspec(); (x, x) ≠ (unspec(), unspec())`

              but

              `let x = unspec(); (x, x) <- (unspec(), unspec())`

              Note: for `nondet`, people will think Prolog rather than C
          - And this depends both _usage_ and _effect_ of sub-expressions, so we need to track both

              `let x = unspec(); e = e` for `e ∉ fv(x)`

              On the other hand,

              `let x = ub(); e -> [ub()/x]e`

              but

              `let x = ub(); e = e` if `e` _pure_ and `x ∈ fv(e)`.

              - In power paper:
                
                - Axiomatization of `ub` is:
                  - I can send it forwards in time
                  - I can replace it with anything
                - _Therefore_, when combined with `case`
                  - I can send arbitrary information about anything _purely_ computable forwards in time
                  - I can safely _remove_ information sent forwards in time, so my compiler can do this aggressively
          - So, let's start with λiter
            - Type theory of λiter with _only effects_
            - Type theory of λiter with _only quantities_
              
]


Directly optimizing a source language can be difficult,
because surface languages are often very large and have features
(such as type inference and overloading)
which make it difficult to express sound program equivalences.
On the other hand, compiling naïvely to executable code and _then_ optimizing is equally challenging,
if it is even feasible to write a one-pass compiler for a given high-level language at all. 
This is because, 
just as programming languages are designed to be written (and hopefully, read) by humans, 
machine code is designed to be efficiently _executed_ by hardware (or an interpreter), 
and is therefore often difficult both to analyze and to generate from high-level constructs.
//
Compiler writers deal with this by using _intermediate representations (IRs)_:

#scaffold[
  - Like programming languages, they are designed to be read and written, rather than executed, but
  - Like executable code, they are designed to be processed by _machines_, rather than people

  - A good IR is simple: has a few features which compose well together
  - It's easy to _generate_ from high-level source code
  - But it also has lots of _invariants_, making it easy to _analyze_ and _rewrite_ while preserving soundness
    - Talk about analysis passes and dataflow
      - Classical IRs are _very good at this_, but they're often underspecified because of imperativity, see: simulation arguments
    - Talk about _optimization passes_
      - Easy to generate code with correct semantics
        - And, very importantly, easy to _inline_: meaning _compositional_
          - High-level languages often make inlining _hard_ because the normies don't prove   substitution
      - Peephole rewriting is important and needs to be sound
      - Control-flow rewriting is import and needs to be sound
      - _Fusing these_ is often where the suffering begins, see conditional move instruction
    - Talk about abstract interpretation ==> needs to be easy to do induction on, few cases
      - Classical IRs are _very bad at this_; this is our contribution!
  - And it also needs to be easy to _lower_ to executable code
  - Two natural ways to derive an IR
    - Go "upwards" from machine code, regularizing it to make it easier to read, write, and analyze
      - This is the "classical" approach used by compilers like LLVM
    - Go "downwards" from high-level code, desugaring features and making things easier for machines to read, write, and analyze
      - Modern compilers often do this many times as part of _lowering passes_; the first attempt at this is usually called a HIR, and then you can recursively apply this until you get to either assembly (Forth/Lisp style) or the low-level IR defined upwards (the usual). 

        If you apply this to HIR you get MIR
      - In practice, compilers may go back and forth between RTL and SSA; e.g. Rust's MIR is a constrained RTL, which goes to LLVM SSA, which goes down to the SelectionDAG (RTL), which then goes down to ASM (machine code)
    - We have semantics for all these stages except the very top and bottom. Another multi-stage technology along these lines is MLIR, so this naturally acts as a semantics for a well-behaved subset of MLIR

    - Completeness (our big theoretical contributions) means: 
      - _we get to use category theory without any additional assumptions_
      - _we get to check whether our actual models are compatible with standard compiler transformations in an implementation-independent, generalizable manner_
        - Neel says: the completeness theorem means that our equations give us a complete API that both the compiler writer can depend on and the model designer can target. i.e.,
          - This gives us an API which can be shared by
          - Model designers and hardware people, who need to show that their model allows common compiler optimizations by showing that it forms an isotope SSA model
            - Going back, what they need to show is that $ms("SSACongr")(cal(R)) = cal(R)$
              where $cal(R)$ is the set of rewrites validated by their model.

              What we give is the function $ms("SSACongr")(cal(R))$
          
          - Compiler writers, who _need_ to show that their optimizations are compatible with our model + their set of assumptions. You can _always_ do this with a large enough set of assumptions (though of course the assumption might simply be "transformation always holds" since they're allowed to be quantified as long as they respect weakening + substitution)!

            That is, given assumptions $cal(R)$, their optimizations must hold in $ms("SSACongr")(cal(R))$, so we tell them exactly how to derive things from a set of _primitve_ assumptions in a model-independent way: the compiler writers only need the kernel generating the assumptions, not either the entire set of assumptions or the model (which are basically the same thing if you're a classical mathematician).
]

#todo[what is an IR]

#todo[what is SSA at a high level; briefly describe RTL as part of the "up from assembly narrative"]

#todo[our actual contributions and why they matter]

#todo[
  Not a thesis statement (Neel); contributions:
  - We give a formal framework for reasoning about SSA
  - We give a categorical semantics
  - We show these are the _same_: sound and _complete_
  - We use this to talk about imperative programming in general (RTL lore)
]

= Static Single Assignment (SSA)

== From RTL to SSA

#todo[what is RTL, and why is it a cool IR, in more detail]

One of the earliest compiler IRs introduced is _register transfer language_ (_RTL_) @allen-70-cfa,
commonly referred to as _three-address code_.
An RTL program consists of a _control-flow graph_ (CFG) $G$
with a distinguished, nameless entry block.
Each node of the CFG corresponds to a _basic block_ $β$,
which is a straight-line sequence of _assignments_ $x = f(y, z)$
// (hence the name _3-address code_, referring to the typical three variables $x, y, z$)
followed by a _terminator_ $τ$,
which tells us where to transfer control next.

In @rtl-grammar, we give a formal presentation of the syntax of RTL parametrized by a set of
_primitive instructions_ $p ∈ cal(I)$. 
Our grammar is intentionally minimal, with many important features implemented via syntax sugar:
- _Constants_ $c$ are represented as nullary primitive instructions $c()$.
- _Operations_ $o$ always return a single value of fixed type;
  operations producing multiple values are treated as returning a tuple
- #todo[talk about binding and destructuring, move footnote about $(V)$ here!]
- _Conditional branches_ $ite(x, τ, τ')$ are desugared to 
  _switch-statements_ 
  $
  switchstmt(o, lb("tt"): τ seq lb("ff"): τ')
  $
  where $lb("tt"), lb("ff") ∈ tbool$ are distinguished labels.
  In general, for every finite set of labels $lb("l") ∈ lb("L")$, 
  we postulate an _enumeration type_ with members of the form $lb("l")_lb("L")$;
  where $lb("L")$ is clear from context, we omit it.

#figure(
  placement: auto,
  [
    #grid(
      align: left,
      columns: 3,
      gutter: 1.5em,
      bnf(
        Prod(
          $v$,
          {
            Or[$x$][_variable_]
            Or[$(V)$][_tuple_]
          },
        ),
        Prod(
          $V$,
          {
            Or[$·$][]
            Or[$x, V$][]
          },
        ),
      ),
      bnf(
        Prod(
          $o$,
          {
            Or[$v$][_value_]
            Or[$f med v$][_application_]
          },
        ),
        Prod(
          $f$,
          {
            Or[$p$][_primitive_]
            Or[$lb("l")_lb("L")$][_label_]
          },
        ),
      ),
      bnf(
        Prod(
          $β$,
          {
            Or[$x = o seq β$][_assign_]
            Or[$(V) = o seq β$][_destructure_]
            Or[$τ$][_terminator_]
          },
        ),
      ),
      bnf(
        Prod(
          $τ$,
          {
            Or[$brb(ℓ)$][_branch_]
            Or[$switchstmt(o, B)$][_case_]
          },
        ),
        Prod(
          $B$,
          {
            Or[$·$][]
            Or[$brb(ℓ), B$][]
          },
        ),
      ),
      bnf(
        Prod(
          $β$,
          {
            Or[$β$][_entry block_]
            Or[$G seq ℓ : β$][_labeled basic block_]
          },
        ),
        )
      ),
  ],
  caption: [
    Grammar for RTL. 
    Note that variable lists $V$ may appear on both the left-hand side and right-hand side of 
    assignments.
  ],
  kind: image,
) <rtl-grammar>

As a concrete example,
consider the simple imperative program to compute $10!$ given in @imperative-factorial.
We can compile this program into RTL, yielding the code in @rtl-factorial, by:
- Converting composite
  like $a * (i + 1)$
  into a sequence of definitions naming each subexpression.
  Here, expressions like $a + b$ are syntactic sugar for primitive operations $+ (a, b)$.
- Converting structured control flow (e.g., $ms("while")$) into unstructured jumps 
  between basic blocks, generating labels $lb("body")$ and $lb("loop")$ as necessary.
  While, in our formalism, the entry block has no name, 
  we will adopt the convention of assigning it the label $lb("entry")$.

  In general, we refer to the basic block with label $lb("label")$ as $β_lb("label")$.

  #todo[in general how to do this obviously depends on the source language; we given an algorithm for WHILE in bleh]

#subpar.grid(
  placement: auto,
  align: bottom,
  figure(
    [$
      & klet n = 10 seq \
      & klet kmut i = 1 seq \
      & klet kmut a = 1 seq \
      & kwhile i < n thick { \
      & quad a = a * (i + 1) \
      & quad i = i + 1 \
      & } \
      \
      \
      \
      \
      \
    $],
    caption: [
      As an imperative program \ \
    ],
  ),
  <imperative-factorial>,

  figure(
    [$
                  & n = 10 seq \
                  & i = 1 seq \
                  & a = 1 seq \
                  & kbr lb("loop") seq \
      lb("loop"): & ite(i < n, brb(lb("body")), retb(a)) seq \
      lb("body"): & t = i + 1 seq \
                  & a = a * t seq \
                  & i = i + 1 seq \
                  & kbr lb("loop") \
                  \
    $],
    caption: [
      As RTL \ \
    ],
  ),
  <rtl-factorial>,

  columns: (1fr, 1fr),
  caption: [
    A simple, slightly suboptimal program to compute 10! via multiplication in a loop,
    represented as typical imperative code and in RTL.
  ],
)

#todo[
  fix this text:

  incorporate the standard constprop/GVN/SCCP SSA argument
  - stick with just constant propagation
  - abstractly, "want to lookup a variable's definition fast because this is good and dataflow is bad"
    - notice: in RTL we want to do this _a lot_
    - So we need to do a dataflow analysis to figure out this information
    - And then carry this information around in our other analyses...
    - But it breaks over and over again
    - RTL + this analysis is just SSA, so why not keep it around
      - As a fun aside, LLVM actually breaks SSA _all the time_ but then recomputes it. That's why we don't _always_ use SSA, some phases are better for RTL...
]

While three-address code is dramatically simpler to reason about than high-level imperative languages,
everything is complicated by the fact that variable may have multiple definitions.
For example, the definition of dominance above uses a set of definitions $ms("defs")(x)$,
Likewise
because a variable's value may be set by multiple definitions throughout the program's execution,
variables do not have stable values,
and so it is not in general safe to substitute a definition for a variable.

To improve our ability to reason about programs,
we introduce the _static single assignment_ restriction,
originally proposed by @alpern-88-ssa-original,
which states that every variable must be defined at exactly one point in the program.
Because there is a unique definition for each variable, substitution is valid.
We can intuitively think of each variable as being defined by an immutable $ms("let")$-binding,
and a variable $x$ is in scope at a program point $P$,
if and only if its _unique_ definition site $D_x$ dominates $P$.

A given basic block can be converted to SSA form by numbering each definition of a variable,
effectively changing references to $x$ to references to $x_t$, i.e. "$x$ at time $t$."
For example, we could rewrite
#todo[fix alignment here, because this bothers me...]
#align(center, stack(
  dir: ltr,
  spacing: 3em,
  $& x = 3y + 5 ; \ & x = 3x + 2; \ & retb((3x + 1))$,
  align(horizon, $≈$),
  $& x_0 = 3y + 5 ; \ & x_1 = 3x_0 + 2 ; \ & retb((3x_1 + 1))$,
))
This transformation enables algebraic reasoning about expressions involving each $x_t$.
However, since we can only define a variable once in SSA form,
expressing programs with loops and branches becomes challenging.
For example,
naïvely trying to lower the program in @rtl-factorial into SSA form would not work,
since the reference to $i$ in the right-hand-side of the statement $i = i + 1$
can refer to _either_ the previous value of $i$ from the last iteration of the loop
_or_ the original value $i = 1$.
The classical solution is to introduce _$ϕ$-nodes_,
which select a value based on the predecessor block from which control arrived.
We give the lowering of our program into SSA with $ϕ$-nodes in @ϕ-factorial

Cytron et al. @cytron-91-ssa-intro
introduced the first efficient algorithm to lower a program in RTL to valid SSA
while introducing a minimum number of $ϕ$-nodes,
making SSA practical for widespread use as an intermediate representation.
Unfortunately, $ϕ$-nodes do not have an obvious operational semantics.

Additionally,
they require us to adopt more complex scoping rules than simple dominance-based scoping.
For example, in the basic block $lb("loop")$ in @ϕ-factorial,
$i_0$ evaluates to 1 if we came from $lb("entry")$ and to $i_1$ if we came from $lb("body")$.
Similarly,
$a_0$ evaluates to either 1 or $a_1$ based on the predecessor block.
This does not obey dominance-based scoping,
since $i_0$ and $i_1$ are defined _after_ the $ϕ$-nodes $i_0$, $a_0$ that reference them,
which seems counterintuitive -- after all, variables are typically used after they are defined.
In fact,
since the value of a $ϕ$-node is determined by which basic block is our immediate predecessor,
we instead need to use the rule that expressions in $ϕ$-node branches with source $S$
can use any variable $y$ defined at the _end_ of $S$.
Note that this is a strict superset of the variables visible for a normal instruction $i$,
which can only use variables $y$ which _dominate_ $i$ -- i.e.,
such that _every_ path from the entry block to the definition of $i$ goes through $y$,
rather than only those paths which also go through $S$.

#todo[color @ϕ-factorial listing to match TOPLAS paper...]

#subpar.grid(
  placement: auto,
  align: bottom,

  figure(
    [$
                  & n = 10 seq \
                  & i = 1 seq \
                  & a = 1 seq \
                  & kbr lb("loop") seq \
      lb("loop"): & ite(i < n, brb(lb("body")), retb(a)) seq \
      lb("body"): & t = i + 1 seq \
                  & a = a * t seq \
                  & i = i + 1 seq \
                  & kbr lb("loop") \
                  \ \ \ \ \ \
    $],
    caption: [
      As RTL \ \
    ],
  ),
  <rtl-factorial2>,

  figure(
    [$
                  & n = 10 seq \
                  & i₀ = 1 seq \
                  & a₀ = 1 seq \
                  & kbr lb("loop") seq \
      lb("loop"): & i₁ = #phistmt($lb("entry") : i₀, lb("body") : i₂$) \
                  & a₁ = #phistmt($lb("entry") : a₀, lb("body") : a₂$) \
                  & ite(i₁ < n, brb(lb("body")), retb(a₁)) seq \
      lb("body"): & t = i₁ + 1 seq \
                  & a₂ = a₁ * t seq \
                  & i₂ = i₁ + 1 seq \
                  & kbr lb("loop") \
                  \
    $],
    caption: [
      A SSA with ϕ-nodes \ \
    ],
  ),
  <ϕ-factorial>,

  columns: (1fr, 1fr),
  caption: [
    A simple, slightly suboptimal program to compute 10! via multiplication in a loop,
    represented as typical imperative code and in RTL.
  ],
)

While this rule can be quite confusing,
and in particular makes it non-obvious how to assign an operational semantics to $ϕ$-nodes,
the fact that the scoping for $ϕ$-node branches is based on the source block,
rather than the block in which the $ϕ$-node itself appears,
hints at a possible solution.
By _moving_ the expression in each branch to the _call-site_,
we can transition to an isomorphic syntax called basic blocks with arguments (BBA),
as illustrated in @bba-factorial.
In this approach,
each $ϕ$-node -- since it lacks side effects and has scoping rules independent of its position in the basic block,
depending only on the source of each branch --
can be moved to the top of the block.
This reorganization allows us to treat each $ϕ$-node as equivalent to an argument for the basic block,
with the corresponding values passed at the jump site.
Converting a program from BBA format back to standard SSA form with $ϕ$-nodes is straightforward:
introduce a $ϕ$-node for each argument of a basic block,
and for each branch corresponding to the $ϕ$-node,
add an argument to the jump instruction from the appropriate source block.
We give a formal grammar for basic blocks-with-arguments SSA in @bba-grammar.
#footnote[
  Many variants of SSA do not allow variables to appear alone on the right-hand side of assignments,
  such as $x = y; β$.
  We do not incorporate this restriction,
  though we could by normalizing even further and substituting $[y slash x]β$ instead.
]
Note that this grammar no longer needs a separate terminator for returns:
we can treat the return point as a distinguished label (with argument) that a program can jump to.

#figure(
  todo[this],
  caption: todo-inline[BBA grammar]
) <bba-grammar>

#figure(
  todo[this],
  caption: todo-inline[BBA factorial]
) <bba-factorial>

This allows us to use dominance-based scoping without any special cases for $ϕ$-nodes.
When considering basic blocks,
this means that a variable is visible within the block $D$ where it is defined,
starting from the point of its definition.
It continues to be visible in all subsequent blocks $P$
that are strictly dominated by $D$ in the control-flow graph (CFG).
For example, in Figure~#todo-inline[fig:fact-bba]:
- $ms("entry")$ strictly dominates $ms("loop")$ and $ms("body")$;
  thus, the variable $n$ defined in $ms("entry")$ is visible in $ms("loop")$ and $ms("body")$.
- $ms("loop")$ strictly dominates $ms("body")$;
  therefore, the parameters $i_0$, $a_0$ to $ms("loop")$ are visible in $ms("body")$
  without the need to pass them as parameters.
- $ms("body")$ does _not_ strictly dominate $ms("loop")$,
  since there is a path from $ms("entry")$ to $ms("loop")$ that does not pass through $ms("body")$.

== Lexically Scoped SSA

#todo[
  fix this text:
  - first off, address why we should care about scoping, why it's not just a state transformer
  - adjust definitions of dominance to SSA; put stuff about domination by a _set_ in later RTL 
    section
  - then segue to Appel's ideas, and how we can do the equivalence
]

#todo[
  We start by introducing RTL and SSA.

  Everyone already believes in SSA, so the new thing we're trying to convince people of (that they don't know yet) is that _variables should be variables_

  - Not locally nameless _at first_ because we want to use variable names to motivate optimizations like constant propagation
    - We already give the following argument
    - Normally, constant propagation / GVN / SCCP is irritating dataflow
    - We show that in SSA we don't need dataflow; we can just look up the variable's unique definition. So $n^2$ to $n$
    - But, Appel says SSA is just functional programming, and looking up the variable's unique definition is therefore just substitution
    - In general, in the functional world
      - We prove things by induction, so we need binding
      - Our power tools are:
        - Local rewrites (peepholes), which work fine in the regular IR world too!
        - _Substitution_, which is a global rewrite of a pure value; the IR world suffers with this one and SSA makes it easier
        - And that's because SSA _is_ functional programming
        - Our _other_ power tool is abstract interpretation, which is our answer to dataflow analysis
        - To do a good abstract interpretation you need to be able to do induction on your program. But... a graph of state transformers is bad for induction!
        - So we need something to do induction on
        - Thankfully, SSA is functional programming!
      - The other thing abstract interpretation et al give us is that we can interpret functional programs in weird domains, where imperative stuff doesn't make sense
        - But if SSA is functional programming, we can interpret SSA there too!
        - Not part of the main line of the argument, shunt somewhere else; the point of this section is to _get to lexical SSA_
]

#notes[
  Weird syntax idea, we discussed this and you rejected it for TOPLAS but makes sense for thesis:
  no where-blocks, just curly braces.

  Neel says: go do it
]

#todo[
  J Random Semiprogrammer says RTL and WHILE are state transformers on the heap (Neel: stacks, Appel's mind changed).

  We want to explain why thinking about variables as variables is even a good idea at all.
]

#todo[deal with this jump, might want to try another tack since scoping is a later section]

#notes[
  In the original, we put the scoping discussion first because later, when we introducd $ϕ$-nodes, we use the complexity of scoping as part of the argument for why to do BBA.

  But this doesn't make much sense in terms of flow because we want to talk about SSA first and _then_ lexical SSA, and now the stuff about scoping and dominance is split across sections. So go fix that.
]


While functional languages typically rely on _lexical scoping_,
where the scope of a variable is determined by its position within the code's nested structure,
RTL uses a different scoping mechanism based on _dominance_.

Informally, 
we don't want to assign a meaning to programs in which variables are used before they are defined. 
If $cal(D)_x$ and $cal(U)_x$ denote the set of program points at which a variable $x$ is defined and used respectively, 
what we want is that every program execution reaching any point in $cal(U)_x$ must first pass through some element of $cal(D)_x$. 
In general, it is undecidable whether this property holds, 
and so we need to use a safe approximation.

Given a _pointed graph_ $G = (V, E)$ equipped with a fixed _entry node_ $e ∈ V$, 
we say a set of nodes $D$ _dominates_ a node $u$ if every path from $e$ to $u$ must first pass through some $d ∈ D$. 
Likewise, we say a single node $d$ dominates $u$ if ${d}$ does.
If we take 
- $G$ to be our control-flow graph, with vertices basic blocks and edges jumps in the program text
- $e = β_lb("entry")$ to be our entry block
it is clear that if $β₁$ dominates $β₂$ no program execution can reach $β₂$ without first having run $β₁$.
This is an over-approximation of our desired property, 
because some jumps may appear in the program text but never be taken at runtime 
(we call such jumps _unreachable_).

//TODO: just write things in terms of dominator trees, or punt to formalism in CFG section

We note that, in general, the relation on basic blocks "$β₁$ dominates $β₂$" in a CFG $G$ can in 
fact be viewed as a tree rooted at the entry block: every pair of basic blocks 
$β₁, β₂$ have a least common ancestor $β$ which dominates them both.
We call this tree the _dominator tree_ @cytron-91-ssa-intro.
#footnote[
  One edge case is that, by our definition, a basic block $β_lb("dead")$ which is _unreachable_ 
  from $β_lb("entry")$ is dominated by _every_ basic block $β$ in the CFG.
  We will simply assume that every CFG is assigned _some_ dominator tree $ms("dom")(G)$ rooted at 
  $β_lb("entry")$ equal to the graph-theoretic dominance relation on all reachable $(β, β')$, 
  and say that $β$ dominates $β'$ iff $(β, β') ∈ ms("dom")(G)$.
]

It follows that we may consider a variable usage in a block $β$ in-scope if and only if either:
- $x$ is defined earlier in $β$
- The set $ms("defs")(x)$ of basic blocks in which $x$ is defined _stricly_ dominates $β$.

  In general, we say a set of nodes $D$ strictly dominates a node $u$ if $D backslash {n}$ dominates $n$. 
  Likewise, $d$ strictly dominates $u$ if ${d} backslash {u}$ dominates $u$, i.e., 
  if $d$ dominates $u$ and $u ≠ d$ 
  (since no nodes are dominated by the empty set).

Equivalently, we can hew closer to our original definition and instead consider a graph of 
_instructions_, where
- An _assignment_ has a single outgoing edge to the next instruction
- A _terminator_ has an outgoing edge to each target appearing within it
Then, a usage of $x$ in an instruction $i$ is in scope if and only if
$i$ is strictly dominated by the set of assignments to $x$.
This conveniently replicates the traditional definition of a basic block as 
a maximal straight-line sequence of non control-flow instructions.
We will give a more formal treatment of RTL programs as graphs in @cfgs.

An important insight provided by the BBA format,
as discussed by @appel-98-ssa and @kelsey-95-cps,
is that a program in SSA form can be interpreted as a collection of mutually tail-recursive functions,
where each basic block and branch correspond to a function and tail call, respectively.
This yields a natural framework for defining the semantics of SSA and reasoning about optimizations.

A program in SSA, however, is not quite a functional program,
because scoping is dominance-based rather than lexically scoped.
It's easy enough to go from a functional program to SSA: 
just flatten everything, forgetting the scoping information 
(α-renaming labels and variables as necessary to guarantee uniqueness);
the result is trivially dominance-scoped.

Our goal, therefore, 
is to develop a simple strategy to insert brackets into any well-formed SSA program 
(up to permutation of basic blocks)
to obtain a lexically scoped functional program.
Let's begin by focusing on variables.
A block $β$ can only use variables defined in the blocks which dominate it
-- i.e., defined in its ancestors in the dominator tree.
Flipping this around, the variables defined in $β$ can only be _used_ by its descendants; i.e., 
by blocks in its dominator subtree, or _region_, $r = ms("maxRegion")(β)$.
The natural strategy this suggests is therefore to have lexical scopes correspond to subtrees of the
dominator tree. One way to go about this is to:
- Re-order the basic blocks in our SSA program so that they form a breadth-first traversal of the 
  dominator tree
- For every basic block $β$ in the dominator tree, add an opening bracket after that block's label and
  a closing bracket after that block's last descendant in the dominator tree
  -- i.e., such that the blocks between the opening and closing brackets are precisely those dominated by $β$.

In particular, each pair of brackets ${ r }$ encloses:
- A basic block $β$, consisting as usual of assignments $x_i = o_i$ followed by a terminator $τ$
- A sequence of bracketed basic block definitions $ℓ_j : { β_j }$
The rules for variable visibility are the obvious ones: 
$x_i$ is visible in $o_k$ for $k > i$, and in arbitrary $β_j$. 
On the other hand, 
since the child basic blocks $ℓ_j$ correspond to _mutually_ recursive functions, 
we will treat them like a `let rec`, with all $ℓ_j$ visible in each $β_j$.

#todo[but not outside the scope]

To see that this works, consider basic blocks $β_lb("jump")$ and $β_lb("dest")$, where 
$β_lb("jump")$ contains a jump to $β_lb("dest")$, or, equivalently, 
the body of $β_lb("jump")$ tail-calls the function corresponding to $β_lb("dest")$.

Observe that any $β_lb("dom")$ which _strictly_ dominates $β_lb("dest")$ must _also_ dominate 
$β_lb("jump")$, as otherwise, 
- By definition, 
  there is a path from $β_lb("entry")$ to $β_lb("jump")$ which does not pass through $β_lb("dom")$
- And therefore, by appending the jump from $β_lb("jump")$ to $β_lb("dest")$ to this path,
  we obtain a path from $β_lb("entry")$ to $β_lb("dest")$ which does not pass through $β_lb("dom")$
- Contradicting the fact that $β_lb("dom")$ dominates $β_lb("dest")$!

#todo[finish explanation]

/*
On the other hand, if $β_lb("dom")$

In particular, letting $β_lb("parent")$ denote $β_lb("dest")$'s parent in the dominator tree
#footnote[
  Since the entry block has no name, it cannot be called, 
  therefore $β_lb("dest")$ cannot be the entry block and so must have a parent in the dominator tree 
  (which of course might be the entry block).
],
$β_lb("parent")$ must dominate _every_ basic block $β_lb("jump")$ containing a jump to $β_lb("dest")$.


Observe that $β_lb("parent")$ _must_ dominate $β_lb("jump")$, as otherwise, 
- By definition, 
  there is a path from $β_lb("entry")$ to $β_lb("jump")$ which does not pass through $β_lb("parent")$
- And therefore, by appending the jump from $β_lb("jump")$ to $β_lb("dest")$ to this path,
  we obtain a path from $β_lb("entry")$ to $β_lb("dest")$ which does not pass through $β_lb("parent")$
- Contradicting the fact that $β_lb("parent")$ dominates $β_lb("dest")$!


Observe that if $β_lb("call")$ calls the function corresponding to a given basic block $β_lb("def")$,
then $β_lb("def")$

$β₁$ as ancestor in the dominance tree
(as, otherwise, the parent would not actually dominate the block,
since we could get to $β₂$ through $β₁$ without passing through $P$).
Moreover,
the variables _visible_ in $B$ are exactly the variables visible at the end of $P$;
i.e., the variables visible in $P$ and those defined in $P$.

So if we make the dominance tree explicit in the syntax and tie the binding of variables to this tree structure,
then lexical and dominance-based scoping become one and the same.
*/

#todo[
  rework lexical SSA text, we already did this
  - I told you how to make lexical SSA
  - Here's it's grammar
  - A formal analysis of the algorithm and friends is over in the dark places
]

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

== Type-Theoretic SSA

#todo[
  - SSA is great because we can do substitution
  - Lexical SSA is great because we can do induction, but it's also the same thing as SSA, we get _strictly more power_
    - Just like SSA is RTL but we keep reaching definitions around...
      - ϕ-nodes are precisely multiple reaching definitions _reified_
    - Likewise, Lexical SSA is SSA but we keep the dominance tree around
      - And guess what, we need to compute that all the time as well!
      - But it gives us the ability to do induction, so not breaking it is relatively easy since if we _do_ break the dominance tree in general we go from good SSA to ill-scoped SSA which is invalid
        - So lexical SSA is a much smaller jump from SSA than SSA is from RTL, since there are valid rewrites which break the SSA property but leave us with valid RTL, but there's no real way to rewrite valid SSA while breaking the dominance tree since that also breaks scopin
]

#todo[
  - I want a substitution principle for SSA so I'm going to extend instructions to expressions
  - We want value substitutions and loops are not values
]

#todo[
  Neel says no:
  - We start with $ms("SSA")(ms("Inst"))$
  - We want substitution to work
  - We have $∀E, ms("Subst")(E) ==> ms("Subst")(ms("SSA")(E))$
  - Alas, $¬ms("Subst")(ms("Inst"))$
  - But, $∀E, ms("SSA")(E) ≅ ms("SSA")(ms("Inst"))$
  - So pick an $E$
    - Cranelift says $ms("ETree")(ms("Inst"))$
    - Let's go max generality and say λiter
]

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
$
  where(letstmt(x, a, brb(ℓ, b)), wbranch(ℓ, y, r))
  equiv where(letstmt(x, a, letstmt(y, b, r)), wbranch(ℓ, y, r))
$
While both sides of this equation are valid lexical SSA programs,
by loosening our syntax slightly,
we can _unconditionally_ replace jumps with regions,
without worrying about jumps nested in case statements or fusing $ms("where")$-blocks.
This, especially combined with change (3),
makes it much easier to verify optimizations such as
#todo[clean up optimization here]
$
  & where(
      casestmt2(a, x, brb(ℓ, (ι_r x)), x, brb(ℓ, (ι_l x))),
      wbranch(ℓ, y, casestmt2(y, z, ms("ret") (ι_r z), z, ms("ret") (ι_l z)))
    ) \
  & equiv casestmt2(
      a,
      x, casestmt2(ι_r x, z, ms("ret") (ι_r z), z, ms("ret") (ι_l z)), \
      & #h(2em) x, casestmt2(ι_l x, z, ms("ret") (ι_r z), z, ms("ret") (ι_l z))
    ) \
  & equiv casestmt2(
      a,
      x, ms("ret")(ι_l x),
      x, ms("ret")(ι_r x)
    )
    equiv ms("ret") (casestmt2(a, x, ι_l x, x, ι_r x))
    equiv ms("ret") a
$
by repeatedly applying a set of known-good rules,
and, moreover, dramatically simplifies the form of the rules themselves.

#todo[figure: grammar for isotopessa]

#todo[
  What we work towards is:
  - SSA is parametrized by an expression language.
    - The standard one is "one instruction"
    - But, even in practice, Cranelift and friends use expression trees...
    - And fun things like Peggy use fun things like loops
    - We have λiter which everything above is a subset of
  - Separately, _type theoretic SSA_ is parametrized by an expression language
  - Recall the ladder components: 
    - $∀ E . ms("TySSA")(E) ≅ ms("SSA")(E)$
    - $∀ E . ms("TySSA")(E) ≅ ms("TySSA")(ms("Op"))$
]

= Type Theory

#notes[
  - We introduce λiter at the end of section 2 as our expression language
  - We want to mention that our expression language has the same power as SSA and give a pointer to 
    the proof down at the end (post-completeness)
  - Minimize forward references considered harmful
  - 
]

#todo[fuse with refined account of SSA]

We now give a formal account of #todo-inline[isotopessa], starting with the types.
Our types are first order,
and consists of binary sums $A + B$, products $A times.o B$, the unit type $mb(1)$,
and the empty type $mb(0)$,
all parameterised over a set of base types $X in cal(T)$.
We write our set of types as $ms("Ty")(X)$.

#todo[add lore about _quantities/resources/usages_, fix notation]

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

#todo[make things $n$-ary]

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
$
  rupg(σ)_(dot.c) & = σ quad rupg(σ)_(ms("K"), ℓ(A)) & = rupg(σ)_(ms("K")), ℓ(x) |-> brb(ℓ, x) \
  lupg(σ)_(dot.c) & = σ quad lupg(σ)_(ms("K"), ℓ(A)) & = ℓ(x) |-> brb(ℓ, x), lupg(σ)_(ms("K"))
$
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
  (letexpr((x, y), f space a, b)) & equiv (letexpr(z_f, f space a, letexpr((x, y), z, b))) \
                                  & equiv (letexpr(z_a, a, letexpr(z_f, f space z_a, letexpr((x, y), z, b)))) \
                                  & equiv (letexpr(z_a, a, letexpr((x, y), f space z_a, b)))
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
  f(casestmt2(e, x, a, y, b)) & equiv (letexpr(z, casestmt2(e, x, a, y, b), f space z)) \
                              & equiv casestmt2(e, x, letexpr(z, a, f space z), y, letexpr(z, b, f space z)) \
                              & equiv casestmt2(e, x, f space a, y, f space b)
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

This completes the equational theory for #ms()[IsotopeSSA] terms;
in #todo-inline[Section: ssec:completeness],
we will show that this is enough to state a completeness theorem.

== Regions

We now come to the equational theory for regions, which is similar to that for terms, except that we
also need to support control-flow graphs. As before, we will split our rules into a set of
_congruence rules_ and, for each region constructor, _rewriting rules_ based on that
constructor's semantics. Our congruence rules, given in #todo[Figure: fig:ssa-reg-congr-rules], are
quite standard; we have:
- As for terms, #todo-inline[refl], #todo-inline[trans], and #todo-inline[symm] state that
  $lbeq(Gamma, dot, dot, ms("L"))$ is an equivalence relation for all $Gamma$, $ms("L")$.
- Similarly, #todo-inline[let₁], #todo-inline[let₂], #todo-inline[case], and #todo-inline[cfg] state that
  $lbeq(Gamma, dot, dot, ms("L"))$ is a congruence over the respective region constructors;
  _as well as_ the equivalence relation on terms $tmeq(Gamma, epsilon, dot, dot, A)$.
- #todo-inline[initial] states that any context containing the empty type $mb(0)$ equates all
  regions, by a similar reasoning to the rules for terms. Note that we do not require an analogue to
  the #todo-inline[terminal] rule (for example, for regions targeting $ms("L") = lhyp(ℓ, mb(1))$),
  since it will follow from the version for terms; this is good, since the concept of a "pure"
  region has not yet been defined.

Our rewriting rules for unary #ms()[let]-statements, given in #todo[Figure: fig:ssa-reg-unary-let], are
analogous to those for unary #ms()[let]-expressions:
- #todo-inline[let₁-β] allows us to perform $beta$-reduction of _pure_ expressions
  into regions; unlike for terms, we do not need an $eta$-rule
- Exactly like for #ms()[let]-expressions, #todo-inline[let₁-op], #todo-inline[let₁-let₁],
  #todo-inline[let₁-let₂], #todo-inline[let₁-abort], and #todo-inline[let₁-case] allow us to pull out nested
  subexpressions of the bound value of a #ms()[let]-statement into their own unary #ms()[let]-statement

Similarly to expressions, binary #ms()[let]-statements and #ms()[case]-statements need only the obvious
$beta$ rule and binding rule, with all the interactions with other constructors derivable; these
rules are given in #todo[Figure: fig:ssa-reg-let2-case-expr]. Note in particular that $eta$-rules are
not necessary, as these are derivable from binding and the $eta$-rules for expressions.

#todo[Figure: Congruence rules for #ms()[IsotopeSSA] regions.
  Rules: refl, trans, symm, let₁, let₂, case, cfg, initial]

#todo[Figure: Rewriting rules for #ms()[IsotopeSSA] unary #ms()[let]-statements.
  Rules: let₁-β, let₁-op, let₁-let₁, let₁-let₂, let₁-case, let₁-abort]

#todo[Figure: Rewriting rules for #ms()[IsotopeSSA] binary #ms()[let]-statements and #ms()[case]-statements.
  Rules: let₂-pair, let₂-bind, case-inl, case-inr, case-bind]

Dealing with #ms()[where]-blocks, on the other hand, is a little bit more complicated, as shown by the
number of rules in #todo[Figure: fig:ssa-where-rules]. One difficulty is that, unlike the other region
constructors, we will need an $eta$-rule as well as _two_ $beta$-rules. The latter are simple
enough to state:
- For $ℓ_k$ defined in a #ms()[where]-block, #todo-inline[cfg-β₁] says that we can replace a
  branch to $ℓ_k$ with argument $a$ with a #ms()[let]-statement binding $a$ to the corresponding
  body $t_k$'s argument $x_k$.
- For $kappa$ _not_ defined in a #ms()[where]-block, #todo-inline[cfg-β₂] says that
  a branch to $kappa$ within the #ms()[where]-block has the same semantics as if the #ms()[where]-block
  was not there; hence, it can be removed.

To state our $eta$-rule, however, we will need to introduce some more machinery. Given a mapping
from a set of labels $ℓ_i$ to associated regions $t_i$, we may define the _control-flow
graph substitution_ $cfgsubst((wbranch(ℓ_i, x_i, t_i),)_i)$ pointwise as follows:
$
  cfgsubst((wbranch(ℓ_i, x_i, t_i),)_i) space kappa space a
  := (where(brb(kappa, a), (wbranch(ℓ_i, x_i, t_i),)_i))
$
In general, we may derive, for any label-context $ms("L")$ (assuming $cfgsubst(dot)$ acts uniformly
on the labels $kappa$ in $ms("L")$ as described above), the following rule #todo-inline[cfgs].

Our $eta$-rule, #todo-inline[cfg-η], says that any #ms()[where]-block of the form
$where(r, (wbranch(ℓ_i, x_i, t_i),)_i)$ has the same semantics as the label-substitution
$[cfgsubst((wbranch(ℓ_i, x_i, t_i),)_i)]r$, which in effect propagates the where-block to the
branches of $r$, if any. While we called this rule #todo-inline[cfg-η], it also functions similarly
to a binding rule in that it allows us to derive many of the expected commutativity properties of
#ms()[where]; for example, we have that
$
  where(letexpr(y, a, r), (wbranch(ℓ_i, x_i, brb(ℓ_j, a_j)),)_i)
  &equiv [cfgsubst((wbranch(ℓ_i, x_i, brb(ℓ_j, a_j)),)_i)](letexpr(y, a, r)) \
  &equiv letexpr(y, a, [cfgsubst((wbranch(ℓ_i, x_i, brb(ℓ_j, a_j)),)_i)]r) \
  &equiv letexpr(y, a, where(r, (wbranch(ℓ_i, x_i, brb(ℓ_j, a_j)),)_i))
$
One particularly important application of the $eta$-rule for control-flow graphs is in validating
the rewrite #todo-inline[case2cfg], which allows us to convert a #ms()[case]-statement into a #ms()[where]-block with two branches.

In addition, we also add as an axiom the ability to get rid of a
single, trivially nested #ms()[where]-block; this is given as the rule
#todo-inline[codiag].


To be able to soundly perform equational rewriting, we will need the _uniformity_ property,
which is described by the rule #todo-inline[uni]. In essence, this lets us commute pure expressions with
loop bodies, enabling rewrites (in imperative style) like
$
  ms("loop") space {x = x + 1 ; ms("if") space p space 3x space {ms("ret") space 3x}}
  quad equiv quad
  y = 3x ; ms("loop") space {y = y + 3 ; ms("if") space p space y space {ms("ret") space y}}
$ <eqn:simple-loop-comm>
Note that substitution alone would not allow us to derive #todo-inline[eqn:simple-loop-comm] above,
since $x$ and $y$ change each iteration, and hence, in SSA, would need to become parameters as
follows:
#todo[eqn:loop-comm-ssa]
The actual rule is quite complicated, so let's break it down point by point. Assume we are given:
- A region $haslb(#$Gamma, bhyp(y, B)$, s, #$ms("L"), kappa(B)$)$ taking "input" $y$ of type
  $B$ and, as "output," jumping to a label $kappa$ with an argument of type $B$. We'll
  interpret branches to any other label (i.e. any label in $ms("L")$) as a (divergent) "side
  effect."
- A region $haslb(#$Gamma, bhyp(x, A)$, t, #$ms("L"), ℓ(A)$)$ taking "input" $x$ of type
  $A$ and, as "output," jumping to a label $ℓ$ with an argument of type $A$.
- A _pure_ expression $hasty(#$Gamma, bhyp(x, A)$, bot, e, B)$ parameterised by a value
  $x$ of type $A$

Suppose further that the following condition holds:
$
  lbeq(
    #$Gamma, bhyp(x, A)$, [e slash y]s, where(t, wbranch(ℓ, x, brb(kappa, e))),
    #$ms("L"), kappa(B)$
  )
$
That is, the following two programs are equivalent:
+ Given input $x$, evaluate $e$ and, taking it's output to be input $y$, evaluate $s$,
  (implicitly) yielding as output a new value of $y$. In imperative pseudocode,
  $
    y = e ; y = s
  $
+ Given input $x$, evaluate $t$ and, taking it's output to be the _new_ value of $x$,
  evaluate $e$, (implicitly) yielding as output a new value $y$. In imperative pseudocode,
  $
    x = t ; y = e
  $

_Then_, for any well-typed entry block $haslb(Gamma, r, #$ms("L"), ℓ(A)$)$ (which can produce
an appropriate input $x : A$ at label $ℓ$), we have that
$
  lbeq(
    Gamma, where(
      (where(r, wbranch(ℓ, x, brb(kappa, e)))),
      wbranch(kappa, y, s)
    ), where(r, t), ms("L")
  )
$
i.e., in imperative pseudocode,
$
  x = r ; y = e ; ms("loop") space {y = s} & equiv x = r ; ms("loop") space {x = t}
$
since
$
  y = e ; y = s ; y = s ; dots.h
  space equiv space
  x = t ; y = e ; y = s ; dots.h
  space equiv space
  x = t ; x = t ; y = e ; dots.h
  space equiv space dots.h
$
where $s$ and $t$ may branch out of the loop.

Note that, due to #todo-inline[let₁-β], #todo-inline[cfg-η], and #todo-inline[cfg-β₁], this is
equivalent to the rule #todo-inline[uni'] shown in #todo-inline[eqn:uni-variant]:
$
  lbeq(
    #$Gamma, bhyp(x, A)$,
    [e slash y]s,
    [ℓ(x) arrow.bar brb(kappa, e)]t,
    #$ms("L"), kappa(B)$
  )
  ==>
  lbeq(
    Gamma,
    (where(([ℓ(x) arrow.bar brb(kappa, e)]r), wbranch(kappa, y, s))),
    (where(r, wbranch(ℓ, x, t))),
    ms("L")
  )
$ <eqn:uni-variant>
where $haslb(Gamma, r, #$ms("L"), ℓ(A)$)$, $hasty(#$Gamma, bhyp(x, A)$, bot, e, B)$,
$haslb(#$Gamma, bhyp(y, B)$, s, #$ms("L"), kappa(B)$)$, and $haslb(#$Gamma, bhyp(x, A)$, t, #$ms("L"), ℓ(A)$)$.
Going back to our concrete example from #todo-inline[eqn:loop-comm-ssa], if we first substitute the
let-binding $y = 3x$ on the RHS, we get the equivalence shown in #todo-inline[eqn:loop-comm-red].
#todo[eqn:loop-comm-red: SSA loop commutation after substitution]

Now, instantiate #todo-inline[uni'] #todo-inline[eqn:uni-variant] by taking:
- $s = letexpr(y', y + 3, ms("if") space p space y' space {ms("ret") space y'} space ms("else") space {brb(kappa, y')})$
  to be the loop body on the RHS
- $e = 3x$
- $r = brb(ℓ, x)$
- $t = letstmt(x', y + 1, ms("if") space p space 3x' space {ms("ret") space 3x'} space ms("else") space {brb(ℓ, x')})$
  to be the loop body on the LHS

It's easy to see that $(where(([ℓ(x) arrow.bar brb(kappa, e)]r), wbranch(kappa, y, s)))$ and
$(where(r, t))$ are syntactically equal to the _RHS_ and _LHS_ of our desired result
#todo-inline[eqn:loop-comm-red]. So, it suffices to verify that
$
  Gamma, bhyp(x, A) &⊢ [e slash y]s \
  &equiv letexpr(y', 3x + 3, ms("if") space p space y' space {ms("ret") space y'} space ms("else") space {brb(kappa, y')}) \
  &equiv letexpr(y', 3(x + 1), ms("if") space p space y' space {ms("ret") space y'} space ms("else") space {brb(kappa, y')}) \
  &equiv letexpr(
    x', x + 1,
    letexpr(y', 3x', ms("if") space p space y' space {ms("ret") space y'} space ms("else") space {brb(kappa, y')})
  ) \
  &equiv letexpr(
    x', x + 1,
    ms("if") space p space 3x' space {ms("ret") space 3x'} space ms("else") space {brb(kappa, 3x')}
  ) \
  &equiv [ℓ(x) arrow.bar brb(kappa, e)]t
$
as desired.

The reason why we require $e$ to be _pure_ in the uniformity rule is that impure expressions do
not necessarily commute with infinite loops, even if they commute with any finite number of
iterations of the loop. For example, if $ms("hi")$ is some effectful operation (say, printing
"hello"), it is quite obvious that,
$
  ms("hi") ; x = x + 1 ; ms("if") space x = y space {ms("ret") space y} & equiv
                                                                          x = x + 1
                                                                          ; ms("if") space x = y space {ms("hi") ; ms("ret") space y}
                                                                          ; ms("hi")
$
whereas
$
  ms("hi") ; ms("loop") space {x = x + 1 ; ms("if") space x = y space {ms("ret") space y}}
  &equiv.not
  ms("loop") space {x = x + 1 ; ms("if") space x = y space {ms("hi") ; ms("ret") space y}} ; ms("hi")
$
since, in particular, we may have $y lt.eq x$, in which case the loop will never exit and hence
$ms("hi")$ will never be executed.

#todo[Figure: Rewriting rules for #ms()[IsotopeSSA] #ms()[where]-blocks.
  Rules: cfg-β₁, cfg-β₂, cfg-η, codiag, uni, dinat]

#todo[Figure: Dinaturality for where-blocks (side-by-side code comparison)]

The derivable rule #todo-inline[uni'] (Equation #todo-inline[ref]) illuminates a very important
potential use for uniformity; namely, formalizing rewrites like those in
Figure #todo-inline[ref]. In particular, consider a program of the form
#todo[equation]
where
- $#haslb($Gamma$, $r$, $ms("L"), ℓ(A)$)$
- $#haslb($Gamma, y : B$, $s$, $ms("L"), ℓ(A)$)$
- $#tmseq($Gamma, bhyp(x, A)$, $⊥$, $e$, $B$)$ is pure

Then we have that

#todo[Equation: multline derivation of substitution commutativity]

and therefore that

#todo[Equation: multline derivation of where-block equivalence]

In particular, for example, we can then easily derive the rewrite from Figure #todo-inline[ref]
to Figure #todo-inline[ref] by noting the _equalities_ (an equivalence would be enough, of
course)

#todo[Equation: align derivation showing loop branch equality]

and

#todo[Equation: multline showing let-binding equality]

Rewrites like this are an instance of the principle we call _dinaturality_, which, for
structured control-flow, can be best expressed as an equivalence between the control-flow graphs in
Figure #todo-inline[ref]. Unlike in the case of uniformity, however, this is true even when
the program fragment $P$ is _impure_, since, unlike in the case of general uniformity, we do
not commute $P$ over an infinite number of iterations. Our final rewriting rule, #todo-inline[dinat],
generalises the above rewrite from sequential composition on a structured control-flow graph to
label substitution on an arbitrary control-flow graph.

#todo[Figure: TikZ diagram showing dinaturality on a structured loop (control-flow graph equivalence)]

We require a separate rule for impure dinaturality as it allows us to relate unary and $n$-ary
#ms()[where]-blocks and, in particular, use this relationship to interconvert between data-flow and
control-flow. This means we now have enough equations to derive the flattening of nested
#ms()[where]-blocks:

#todo[Equation: cfg-fuse rule showing where-block flattening with proof tree]

Rather than directly giving derivation trees for such auxiliary rules, it is more convenient to
give a denotational proof. However, the completeness of our equational theory (proved in
Section #todo-inline[ref]) means that the semantic equality implies the existence of the
requisite derivation tree. A proof can be found in Lemma #todo-inline[ref] in the appendix.
This is one of the benefits of having a completeness result: it lets us switch freely between
equational and denotational modes of reasoning.

There are some other basic rules we may want to use which turn out to be
derivable from our existing set. For example, while re-ordering labels in a #ms("where")-block looks
like a no-op in our named syntax, to rigorously justify the following rule actually requires
dinaturality (with the permutation done via a label-substitution):
#todo[permutation]
Note the implicit use of the fact that if some region $r$ typechecks in some label-context $ms(L)$,
then it typechecks in any permutation of $ms(L)$, which is again proven by label-substitution.

== Metatheory

We can now begin to investigate the metatheoretic properties of our equational theory. As a first
sanity check, we can verify that weakening, label-weakening, and loosening of effects all respect
our equivalence relation, as stated in the following lemma:

#todo[fix this...]

*Lemma (Weakening (Rewriting))*: Given $Gamma lt.eq Delta$, $ms("L") lt.eq ms("K")$, and $epsilon lt.eq epsilon'$, we have that

+ $#tmeq([$Delta$], [$epsilon$], [$a$], [$a'$], [$A$]) ==> #tmeq([$Gamma$], [$epsilon'$], [$a$], [$a'$], [$A$])$
+ $#lbeq([$Delta$], [$r$], [$r'$], [ms("L")]) ==> #lbeq([$Gamma$], [$r$], [$r'$], [ms("K")])$

*Proof*: These are formalized as:

+ `Term.InS.wk_congr` and `Term.InS.wk_eff_congr` in
  `Rewrite/Term/Setoid.lean`
+ `Region.InS.vwk_congr` and `Region.InS.lwk_congr` in
  `Rewrite/Region/Setoid.lean`

It is straightforward to verify that these are indeed equivalence relations.  In fact, it turns out
that substitution and label-substitution both respect these equivalences, in the following precise
sense:

*Lemma (Congruence (Substitution))*: Given $#tmseq([$gamma$], [$gamma'$], [$Gamma$], [$Delta$])$, we have that

+ $#tmeq([$Delta$], [$epsilon$], [$a$], [$a'$], [$A$])
  ==> #tmeq([$Gamma$], [$epsilon$], [[[$gamma$]a]], [[[$gamma'$]a']], [$A$])$
+ $#lbeq([$Delta$], [$r$], [$r'$], [ms("L")])
  ==> #lbeq([$Gamma$], [[[$gamma$]r]], [[[$gamma'$]r']], [ms("L")])$
+ $#tmseq([$rho$], [$rho'$], [$Delta$], [$Xi$])
  ==> #tmseq([[[$gamma$]rho]], [[[$gamma'$]rho']], [$Gamma$], [$Xi$])$
+ $#lbseq([$sigma$], [$sigma'$], [$Delta$], [ms("L")], [ms("K")])
  ==> #lbseq([[[$gamma$]sigma]], [[[$gamma'$]sigma']], [$Gamma$], [ms("L")], [ms("K")])$

*Proof*: These are formalized as:

+ `Term.InS.subst_congr` in `Rewrite/Term/Setoid.lean`
+ `Region.InS.vsubst_congr` in `Rewrite/Region/Setoid.lean`
+ `Term.Subst.InS.comp_congr` in `Rewrite/Term/Setoid.lean`
+ `Region.Subst.InS.vsubst_congr` in `Rewrite/Region/LSubst.lean`

In particular, note that this lemma uses an equivalence relation on substitutions and
label-substitutions: this is just the obvious pointwise extension of the equivalence relation on
terms and regions respectively. We give the rules for this relation in
Figure #todo-inline[ref] in the interests of explicitness.

*Lemma (Congruence (Label Substitution))*:
Given $#lbseq($sigma$, $sigma'$, $Gamma$, $ms("L")$, $ms("K")$)$, we have that

+ $#lbeq([$Gamma$], [$r$], [$r'$], [ms("L")]) ==> #lbeq([$Gamma$], [[[$sigma$]r]], [[[$sigma'$]r']], [ms("K")])$
+ $#lbseq([$kappa$], [$kappa'$], [$Gamma$], [ms("L")], [ms("J")])
  ==> #lbseq([[[$sigma$]kappa]], [[[$sigma'$]kappa']], [$Gamma$], [ms("K")], [ms("J")])$

*Proof*: These are formalized as:

+ `Region.InS.lsubst_congr` in `Rewrite/Region/LSubst.lean`
+ `Region.LSubst.InS.comp_congr` in `Rewrite/Region/LSubst.lean`

This means, in particular, that, substitution and label-substitution are well-defined operators on
equivalence classes of terms, which will come in handy later as we set out to prove completeness
in Section #todo-inline[ref].

#todo[Figure: Rules for the equivalence relation on #ms()[IsotopeSSA] substitutions and label-substitutions.
  Rules: sb-nil, sb-cons, sb-skip-l, sb-skip-r, ls-nil, ls-cons, ls-skip-l, ls-skip-r, sb-id, ls-id]

= Control-Flow Graphs

<cfgs>

= Future Work

#todo[literally an infinite pile]

#bibliography("refs.bib", style: "acm-edited.csl")
