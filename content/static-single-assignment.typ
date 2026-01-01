#import "../syntax.typ": *
#import "../todos.typ": *

#context if (thesis-state.get)().is-standalone {
  set document(title: "Static Single Assignment (SSA)")
  title()
}

#show : show-syntax

= From RTL to SSA

#import "rules/intro.typ": *

One of the earliest compiler IRs introduced is _register transfer language_ (_RTL_) @allen-70-cfa,
commonly referred to as _three-address code_.
An RTL program consists of a _control-flow graph_ (CFG) $G$
with a distinguished, nameless entry block.
Each node of the CFG corresponds to a _basic block_ $β$,
which is a straight-line sequence of _assignments_, 
generally of the form $x = f(y, z)$,
#footnote[
  Hence the name "3-address code," referring to the three variables $x, y, z$.
  Assignments $x = y + z$ are often referred to as _quads_ @aho-11-dragon,
  since they have four arguments:
  three variables, and the operator $+$.
]
followed by a _terminator_ $τ$,
which tells us where to transfer control next.

In @rtl-grammar, we give a formal presentation of the syntax of RTL parametrized by a set of
_primitive instructions_ $f ∈ ms("I")$ and _constants_ $c ∈ ms("C")$.

Our grammar is intentionally minimal, with many important features implemented via syntax sugar:
- _Tuples_ $(V)$ are finite collections of named values $fty(lb("f"), v)$;
  anonymous tuples $(v_0,..., v_(n - 1))$ are syntactic sugar for tuples with distinguished names
  $(fexpr(lb("[0]"), v_0),..., fexpr(lb("[n - 1]"), v_(n - 1)))$.

- _Instructions_ $f$ always consume a single value $v$ of fixed type; 
  binary operations like $x + 5$ are desugared to tuple application $+(x, 5)$
- _Operations_ $o$ always produce a single value of fixed type; 
  multiple return values are implemented via tuple destructure.
- _Conditional branches_ $ite(x, τ, τ')$ are desugared to
  _switch-statements_
  $
    sswitch(o, lb("tt"): τ seq lb("ff"): τ')
  $
  where $lb("tt"), lb("ff") ∈ tbool$ are distinguished labels.

#rtl-flat-grammar <rtl-grammar>

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

#rtl-10-fact

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
      - As a fun aside, LLVM actually breaks SSA _all the time_ but then recomputes it. 
        That's why we don't _always_ use SSA, some phases are better for RTL...
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

#ssa-ϕ-10-fact

While this rule can be quite confusing,
and in particular makes it non-obvious how to assign an operational semantics to $ϕ$-nodes,
the fact that the scoping for $ϕ$-node branches is based on the source block,
rather than the block in which the $ϕ$-node itself appears,
hints at a possible solution.
By _moving_ the expression in each branch to the _call-site_,
we can transition to an isomorphic syntax called basic blocks with arguments (BBA),
as illustrated in @bba-factorial.

#figure(
  todo[this],
  caption: todo-inline[BBA factorial],
) <bba-factorial>

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

#ssa-flat-grammar <bba-grammar>

This allows us to use dominance-based scoping without any special cases for $ϕ$-nodes.
When considering basic blocks,
this means that a variable is visible within the block $D$ where it is defined,
starting from the point of its definition.
It continues to be visible in all subsequent blocks $P$
that are strictly dominated by $D$ in the control-flow graph (CFG).
For example, in @bba-factorial:
- $ms("entry")$ strictly dominates $ms("loop")$ and $ms("body")$;
  thus, the variable $n$ defined in $ms("entry")$ is visible in $ms("loop")$ and $ms("body")$.
- $ms("loop")$ strictly dominates $ms("body")$;
  therefore, the parameters $i_0$, $a_0$ to $ms("loop")$ are visible in $ms("body")$
  without the need to pass them as parameters.
- $ms("body")$ does _not_ strictly dominate $ms("loop")$,
  since there is a path from $ms("entry")$ to $ms("loop")$ that does not pass through $ms("body")$.

= Lexical SSA

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

#todo[
  J Random Semiprogrammer says RTL and WHILE are state transformers on the heap (Neel: stacks, Appel's mind changed).

  We want to explain why thinking about variables as variables is even a good idea at all.
]

#todo[deal with this jump, might want to try another tack since scoping is a later section]

#block-note[
  In the original, we put the scoping discussion first because later, when we introducd $ϕ$-nodes, we use the complexity of scoping as part of the argument for why to do BBA.

  But this doesn't make much sense in terms of flow because we want to talk about SSA first and _then_ lexical SSA, and now the stuff about scoping and dominance is split across sections. So go fix that.
]

#todo[text]

#todo[convert factorial to lexical SSA]



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
// We will give a more formal treatment of RTL programs as graphs in @cfgs.

An important insight provided by the BBA format,
as discussed by @appel-98-ssa and @kelsey-95-cps,
is that a program in SSA form can be interpreted as a family of mutually tail-recursive functions,
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
rather than treating the control-flow graph $G$ as a flat family of basic blocks
(with a distinguished block),
to instead consider (subtrees of) the dominance tree $r$,
with the root of the tree implicitly being the entry block.
We call such subtrees _regions_:
we note that they have a single entry (the root) and multiple exits (the leaves),
and so generalize the more standard concept of a single-entry-single-exit region in a CFG.

In particular,
a _region_ $r$ generalizes a basic block $β$ by annotating the terminator $τ$
with a list $L$ of _labeled branches_ #todo-inline[or w branch...]//"$wbranch(ℓ_i, x_i, t_i)$,"
yielding a _$ms("where")$-block_ " #todo-inline[no more where...] //$where(τ, L)$."
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

#lex-ssa-op-grammar <lex-ssa-op-grammar>

= Expressions and Substitution

#todo[
  Separate evolution steps:
  1. Expression language, in steps
  2. Add braces
  3. Add 
]

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
+ Extending expressions $a$ to allow _let-expressions_ "$elet(x, a, b)$"
  and _case-expressions_ "$ecase2(a, x, b, y, c)$" <ssa-change-expr>

#todo[while rewriting, make sure to fix numbering]

This leaves us with our final language, #ssa-calc,
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
#todo[no more where]
/*
$
  where(letstmt(x, a, brb(ℓ, b)), wbranch(ℓ, y, r))
  equiv where(letstmt(x, a, letstmt(y, b, r)), wbranch(ℓ, y, r))
$
*/
While both sides of this equation are valid lexical SSA programs,
by loosening our syntax slightly,
we can _unconditionally_ replace jumps with regions,
without worrying about jumps nested in case statements or fusing $ms("where")$-blocks.

#ssa-expr-grammar <iter-calc-grammar>

#lex-ssa-grammar <lex-ssa-grammar>

= Control-Flow Rewriting

#lex-ssa-brace-grammar <lex-ssa-brace-grammar>

#todo[text]

#tt-ssa-grammar <tt-ssa-grammar>

#context if (thesis-state.get)().is-standalone {
  the-bibliography
}
