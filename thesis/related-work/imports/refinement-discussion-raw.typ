// Mechanical transcription from:
// papers/isotope/complete-refinement-ssa.tex
// Repository commit: 9480278f2503902f0fa632d05d7f0c8faae893f3
// Section: Discussion and Related Work
// Source lines: 3205--3308
// Conversion: prose preserved verbatim; LaTeX presentation translated mechanically to Typst.

#import "/lib/prelude.typ": *

= Discussion and Related Work
<refall:discussion-and-related-work>
#strong[From SSA to FP] SSA was introduced as a compiler IR by
#cite(<alpern-ssa-original-88>, form: "prose") and
#cite(<rosen-gvn-1988>, form: "prose"), with the goal of simplifying
reasoning about variable values. In three address code, a variable is
mutable and can have a different value at each program point, whereas in
SSA, each variable has a single abstract value, a fact which greatly
simplifies optimizations like global value numbering.
#cite(<kelsey-95-cps>, form: "prose") demonstrated a correspondence
between SSA and a fragment of continuation-passing style, and
#cite(<appel-ssa>, form: "prose") simplified this further and showed
that an SSA program can be seen as a group of procedures mutually
tail-calling each other. When the dominance tree is further made
explicit in the syntax, we recover lexical scoping, and
#cite(<chakravarty-functional-ssa-2003>, form: "prose") used this to
show how to translate SSA programs into ANF.
#cite(<ghalayini-24-ssa-densem-arxiv>, form: "prose") relaxed the ANF
restriction to permit compound (pure) expressions, which gives a
calculus with better substitution principles, but which still has
explicit block definitions. In this work, we take the final step and
give a fully expression-oriented syntax, which is still completely
equivalent to traditional SSA.

#strong[Semantics of SSA] #cite(<vellvm-12>, form: "prose") is a
mechanized semantics for LLVM's SSA dialect. Their syntax closely
follows LLVM's, and so their operational semantics must compute
$phi.alt$-nodes at each step. Furthermore, they give several such
semantics and prove refinements between them. Each semantics is further
parameterized over a memory model, and so execution builds a tree of
possible executions, resumption-style, which can then be made into
concrete execution traces with an "effect handler" or free monad
interpreter computing the effect of each memory action.
#cite(<garbuzov-structural-cfg-2018>, form: "prose") exhibit a
correspondence between an operational semantics for both SSA and a
fragment of call-by-push-value~#cite(<cbpv>), and then use the normal form
bisimulations of #cite(<lassen-bisim>, form: "prose") to derive an
equational theory for justifying optimizations. This work considers
nontermination as the only effect, and studies equivalence rather than
refinement. #cite(<ghalayini-24-ssa-densem-arxiv>, form: "prose") give a
denotational semantics similar to this paper's, but their model is not
in enriched categories and hence does not model refinement, nor does it
model an effect system or linear types.

#strong[Effect Systems and Linearity] Effect systems were introduced by
#cite(<gifford86>, form: "prose"), which introduced a type system with
a lattice of effects to track which effects a program could potentially
perform, with the idea of gaining reasoning principles by restricting
effects. #cite(<fuhrmann-direct-1999>, form: "prose") introduced the
idea of categorizing effects in terms of linearity (i.e., whether
effects can be moved, duplicated or dropped), which reverses the
conceptual priority: effects are classified not by their intension, but
by which equations they validate.
#cite(<kammar-effect-12>, form: "prose") build on this idea, and give a
Gifford-style type-and-effect system for a variant of
call-by-push-value, an effect-dependent equational, and conditions on
the semantics monad to ensure each equation holds. We build on this work
by integrating the idea of linearity of effects with an old idea of
#cite(<lipton-mover-75>, form: "prose"). By simply classifying effects
by whether they can commute to the left or right of another effect, we
gain a very rich (in)equational theory very cheaply.
