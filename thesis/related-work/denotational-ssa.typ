// Verbatim mechanical transcription from:
// papers/isotope/denotational-semantics-of-ssa.tex
// Repository commit: afa82558acf643f53a3e038e635ed9520ace88c6
// Source section: Discussion and Related Work, lines 5218–5617

#import "/lib/prelude.typ": *
#show: chapter.with(title: "Discussion and Related Work")

== Lean Formalization
We have formalized many of the lemmas and theorems presented in this
paper in the Lean 4 proof assistant; as of now, our main formalization,
`debruijn-ssa` (#link("https://github.com/imbrem/debruijn-ssa")),
weighs about ~29 kloc. While our paper uses named variables for
simplicity, all our rules and syntax are formalized using de-Bruijn
indices. Each formalized theorem is tagged as such in the respective
proof. It was also necessary to fork Mathlib's monoidal category
implementation to support Freyd categories, distributivity, and Elgot
structure: the resulting library, `discretion`
(#link("https://github.com/imbrem/discretion")), weighs about ~27 kloc.
We are currently trying to upstream support for premonoidal categories
into Mathlib.

#todo[Re-audit these mechanization and upstreaming claims against the current Lean repositories before thesis or TOPLAS integration.]

== SSA, FP and IRs
Static Single Assignment (SSA) form was first introduced as a compiler
intermediate representation by
#cite(<alpern-ssa-original-88>, form: "prose") and
#cite(<rosen-gvn-1988>, form: "prose"), with the goal of facilitating
effective reasoning about program variable equivalence. To perform
optimizations like common subexpression elimination (CSE) effectively,
we need to determine which expressions are equal #emph[at a given point
in time]. By transforming the program into SSA form, we introduce
unique variables for each assignment and use $phi.alt$-nodes to merge
variable values at points where control paths converge. Since each
variable then corresponds to a unique value at a specific point in the
program's execution, SSA unlocks the ability to perform #emph[algebraic
reasoning] about variable values over time. As a result, analyses like
CSE become a matter of simple algebraic rewriting based on variable
names.

#cite(<cytron-ssa-intro-91>, form: "prose") provided the first efficient
algorithm for converting 3-address code programs to SSA form using a
minimal number of $phi.alt$-nodes. They observed that a $phi.alt$-node
only needs to be introduced at the earliest point where a variable may
have different values based on control flow. This point is computable
via the graph-theoretic notion of a #emph[dominance frontier], which
identifies where control paths merge in the program's control flow
graph. Since then, SSA has become the intermediate representation of
choice for most production-grade compiler toolchains.

One of the most famous optimizations enabled by SSA's support for
effective algebraic reasoning is #emph[sparse conditional constant
propagation (SCCP)], introduced in
#cite(<wegman-sccp-91>, form: "prose"). This algorithm leverages the
SSA property to reason about the possible set of values each variable
may take using a lattice-based data-flow analysis, which models variable
values in terms of abstract states like #emph[unknown],
#emph[constant], or #emph[overdefined]. Without SSA, one could naively
consider all variable definitions, which would likely detect fewer
constants due to imprecision. Alternatively, achieving more precise
results would require a complex and computationally intensive
reaching-definitions analysis.

However, while SSA is an excellent representation for implementing
compilers, the semantics of $phi.alt$-nodes can be quite unintuitive due
to their lack of an obvious operational interpretation, making them
challenging to reason about formally.
#cite(<kelsey-95-cps>, form: "prose") establishes a correspondence
between SSA and a subset of #emph[continuation-passing style (CPS)], a
common intermediate representation for functional compilers. In
particular, while not all CPS programs can be directly converted to SSA
form---those using non-local returns like `longjmp` or `call/cc`---the
typical outputs of CPS transformations avoid such features. Kelsey
observed that many optimizations requiring flow analysis in CPS could be
performed directly in SSA, often dramatically simplifying them.

#cite(<appel-ssa>, form: "prose") builds on this work by informally
showing that the functional subset of CPS programs “hidden inside" SSA
is, in fact, simply nested, mutually tail-recursive functions, with each
function corresponding to a basic block. He makes the key observation
that the dominance-based scoping of SSA corresponds to the lexical
scoping of functions. For a variable to be visible in a function, it
must appear in the lexical scope of that variable's definition and
therefore be dominated by it; otherwise, there would be no way to call
the function.

In fact, the subset of functional programs identified by
#cite(<appel-ssa>, form: "prose") corresponds to #emph[A-normal form
(ANF)], another functional intermediate representation advocated by
#cite(<flanagan-93-anf>, form: "prose").
#cite(<chakravarty-functional-ssa-2003>, form: "prose") formalizes this
correspondence giving an algorithm to convert SSA programs to ANF, and
then showing how SSA optimizations such as SCCP can be written to
operate on ANF programs. The authors highlight that the semantic rigor
of their notation, combined with the well-defined semantics of ANF, make
their presentation of SCCP significantly more amenable to formal
analysis.

Going in the other direction, #cite(<thorin-12>, form: "prose")
introduce the Thorin intermediate representation, which consists of CPS
extended with SSA-style dominance-based scoping. As SSA is a first-order
language, it is often difficult to represent programs using closures
effectively, and consequently, difficult to optimize them well. The
authors give the example of LLVM, which often needs to generate a new
struct and a large amount of boilerplate code for every closure, which,
even after optimization, is often not significantly reduced. By
contrast, Thorin retains the advantages of CPS for representing
functional programs, while enabling SSA-like graph-based use-def
analysis by prohibiting variable shadowing.

The primary focus of the works we have covered so far is establishing
the correspondence between SSA, an imperative intermediate
representation, and widely used functional intermediate representations.
However, to advance beyond these correspondences and directly study the
optimization and verification of SSA programs themselves, we require an
equational theory underpinned by formal semantics. One approach found in
the literature (and which we also use) is to relax SSA into forms that
support richer substitution principles and well-defined operational
semantics, which can then be used to reason about SSA itself. Two papers
which exemplify this approach are
#cite(<benton-kennedy-99>, form: "prose") and
#cite(<garbuzov-structural-cfg-2018>, form: "prose").

One of the difficulties of working with ANF as an intermediate
representation is that it does not, in general, satisfy
#emph[substitution]: replacing a variable $x$ with a compound
expression like a function call can take a program out of the
ANF-fragment. The #emph[monadic intermediate language (MIL)] introduced
by #cite(<benton-kennedy-99>, form: "prose") for use in the MLj compiler
for Standard ML can be viewed as a relaxation of ANF (and hence, of SSA)
to get a nicer substitution principle. Benton and Kennedy then use this
flexibility to build up an equational theory justified by their
operational semantics. One interesting feature is that, unlike Moggi's
equational metalanguage @moggi-91-monad (and like our $lambda_(sans("SSA"))$ calculus), MIL
enforces a stratification of #emph[values] and #emph[computations],
without supporting "computations of computations" (corresponding to
nested monad types $sans("T")(sans("T")(A))$). This hints at Freyd
categories, rather than general Kleisli categories, being a natural
model of MIL-like intermediate representations.

Similarly, #cite(<garbuzov-structural-cfg-2018>, form: "prose") exhibit
a correspondence between an operational semantics for SSA and an
operational semantics for call-by-push-value (CBPV) @cbpv. They then use
the normal form bisimulations of #cite(<lassen-bisim>, form: "prose") to
derive an equational theory for use in justifying optimizations. In
particular, we can view their paper as interpreting CBPV as a relaxation
of SSA more suited for developing an equational theory and for semantics
work; in particular, to be able to take advantage of CBPV to give a
#emph[structural] operational semantics for (unstructured) SSA programs.
The semantics of CBPV are widely studied, and hint at a large variety of
potential models for SSA, but the formalization in
@garbuzov-structural-cfg-2018 does not support any effects other than
nontermination.

== Formalizations of SSA
=== Other SSA type systems
Several attempts have been made to provide a type-theoretic treatment of
SSA. The work most similar to ours is by
#cite(<typed-effect-ssa-rigon-torrens-vasconcellos-20>, form: "prose"),
who present a typed translation from SSA into the lambda calculus using
a type-and-effect system, observing that the algorithm for converting
programs to SSA form may also be viewed as a mechanism for transforming
programs in a functional language with unstructured control flow into
equivalent expressions.

Similarly to $lambda_(sans("SSA"))$, they extend the lambda calculus with a mutually recursive
`where`-binding, which allows them to directly translate unstructured
SSA control flow. However, their calculus uses only a single syntactic
category of expressions, whereas we attempt to model (generalized) SSA
directly by distinguishing between expressions and regions. Their
language also includes support for effect handlers, which are beyond the
scope of our current study but represent an interesting direction for
future work. While the authors do not provide an equational theory or a
semantics for their language, we believe that our equational theory
could be adapted to the fragment of their language without effect
handlers.

An interesting alternative approach is demonstrated by
#cite(<ssa-types-matsuno-ohori-06>, form: "prose"), who give a type
theory for what appear to be ordinary three-address code programs.
However, every well-typed program can be placed into SSA-form by
inserting $phi.alt$-nodes in a fully type-directed way. This lets them
model SSA without any $phi.alt$-nodes, letting them use the standard
semantics for three-address code.

#cite(<menon-verified-06>, form: "prose") give a type-safe formalization
of SSA, along with an operational semantics and formal definitions of
dominance, definition/use points, and the SSA property for 3-address
code. By augmenting SSA with first-class proof variables, they aim to
give a representation which allows aggressive optimizations to preserve
safety information. Their type system requires checking the SSA property
separately from well-typedness, but is proven sound if the SSA property
holds. #cite(<hua-explicit-ssa-2010>, form: "prose") give another type
system and direct operational semantics for standard SSA, and prove type
safety for it.

Many operational semantics for SSA have arisen from compiler
verification efforts. #cite(<barthe-compcert-ssa-2014>, form: "prose")
give an operational semantics as part of the CompCertSSA project, and
give a semantics-preserving translation from three-address code into
SSA. #cite(<herklotz-gsa-2023>, form: "prose") formalise "gated SSA"
and give semantics-preserving translations between it and ordinary SSA.
Going beyond CompCertSSA, #cite(<vellvm-12>, form: "prose") have studied
the semantics of the LLVM IR itself as part of the Vellvm project;
#cite(<li-20-kllvm>, form: "prose") goes further and gives an
operational semantics for LLVM in the (sequentially consistent)
multithreaded setting.

There has been much less work on denotational semantics for SSA, or
directly on its equational theory.
#cite(<pop-ssa-inout-2009>, form: "prose") give an unusual denotational
model of SSA in terms of the iteration structure of a program, which
they use to better understand the loop-closing $phi.alt$-nodes found
both in the gated SSA representation as well as practical compilers such
as GCC. #cite(<xia-20-itrees>, form: "prose") describe a toolkit for
building denotational semantics for imperative languages, including the
standard IMP language and a simple assembly language, using the
#emph[interaction tree monad] and #emph[continuation tree monad], which
they show to satisfy the Elgot axioms. Recently,
#cite(<chappe-25-ctrees>, form: "prose") introduced #emph[choice trees]
(CTrees), which extend ITrees to support weak memory concurrency, and
use this to model a subset of LLVM IR.

=== Mechanizations of SSA
CompcertSSA @compcert-ssa-12 is an attempt to extend the CompCert
verified compiler @leroy-compcert-09 with an SSA-based middle-end. This
is achieved by generating a pruned SSA IR from CompCert's RTL format.
Instead of verifying the RTL-to-SSA translation within Coq, this
translation is performed by unverified code, and a separate
#emph[translation validation] stage uses a verified checker to ensure
correctness. After performing (verified) SSA optimizations, the IR is
naively lowered back to RTL for the rest of CompCert's machinery to work
on. #cite(<demange-ssa-15>, form: "prose") build on this work by
providing realistic, verified implementations of Sparse Conditional
Constant Propagation (SCCP) @wegman-sccp-91, Common Subexpression
Elimination (CSE), and Global Value Numbering (GVN) @rosen-gvn-1988
within a general framework of flow-insensitive static analysis for
CompCertSSA.

While CompCert is a verified implementation of a new compiler in Coq,
the Vellvm project @vellvm-12 attempts to mechanize a subset of the LLVM
intermediate representation (IR), covering the LLVM type system,
operational semantics, and the well-formedness and structural properties
of valid LLVM IR. The authors adopt a memory model for LLVM based on
CompCert's @leroy-compcert-09, allowing them to leverage significant
portions of CompCert's Coq infrastructure. Similarly,
#cite(<siddharth-24-peephole>, form: "prose") attempt to mechanize a
well-defined subset of the Multi-Level Intermediate Representation
(MLIR) in the Lean 4 theorem prover. Their formalization features a
user-friendly front end to convert MLIR syntax into their calculus and
scaffolding for defining and verifying peephole rewrites using tactics.
Their framework has been tested on bitvector rewrites from LLVM,
structured control flow, and fully homomorphic encryption; however, as
of publication, only structured control flow was fully supported.

=== Completeness
Most other formalizations oF SSA have given #emph[specific] semantics
for it, whether operational or denotational. One of the features which
makes our work distinctive is that we give our type theory semantics
relative to a categorical axiomatization. Essentially, we have
parameterized our interpretation over any model satisfying the
Freyd-Elgot axioms. First, this lets us show that many different
concrete semantics are valid models of SSA, as can be seen in section 6.
This also let us show that our equational theory is complete: we have
exactly the equations valid in all Freyd-Elgot models, no more and
(crucially) no less. As a result, implementors and researchers proving
things about compiler optimizations do not have to deal with any of the
messy details of (for example) weak memory semantics, unless they are
trying to study optimizations specifically involving weak memory. All
the usual equations used in control- and data-flow optimizations are
independent of those details, and can be validated using the equational
theory.

Conversely, researchers working on models of weak memory (and other
strange models of computation such as quantum computation), can use the
Freyd-Elgot axioms as a target. If they ensure their models satisfy
these axioms, then using an SSA-based IR in their compiler is justified.

== Compositional (Relaxed) Concurrency
The most natural way to think about concurrency is often in terms of an
operational semantics on an abstract machine, in which concurrent
threads interleave and interact. Such semantics, naturally, are designed
to reason about an entire program at a time.
#cite(<batty-compositional-17>, form: "prose") argues that a
compositional semantics of concurrency is necessary to be able to reason
about properties of large software systems effectively, particularly in
the presence of complicating factors such as compiler optimizations and
weak memory semantics. However, it is generally very challenging to
reason about a small component of a concurrent system in isolation since
its behaviour may be drastically affected by other components running in
parallel.

One natural approach to constructing denotational models of concurrency
is to consider the extension of an abstract machine's behavior. Each
thread performs a sequence of atomic actions, and so from the outside,
the machine can produce any interleaving of the atomic actions of each
thread. Just by itself, considering sets of possible traces is not
sufficiently abstract, and so
#cite(<brookes-full-abstraction-96>, form: "prose") takes the closure of
these sets under semantics-preserving transformations, such as
stuttering (introducing extra identity steps) and mumbling (which fuse
sequential atomic operations, thereby hiding implementation details), to
obtain a model with good equational properties such as associativity
($⟦ alpha ; (beta ; gamma) ⟧ = ⟦ (alpha ; beta) ; gamma ⟧$)
and the expected identities for branches and loops.

If the machine model is #emph[sequentially consistent] -- i.e., all
allowed behaviors arise from interleavings of sequences of atomic events
-- then this style of trace semantics is sufficient. However, real
hardware often exhibits #emph[relaxed behaviour], in which additional
behaviours which do not correspond to the interleaving of parallel
threads are allowed. Even more relaxed behaviours arise from fundamental
compiler optimizations, such as re-ordering of independent reads and
writes. These are perfectly valid in a single-threaded context but can
introduce new behaviours in multithreaded programs --- for example,
another thread could distinguish the order of writes. In general, we
need tools to reason about interactions with a system that is not
#emph[linearizable] (i.e., in which concurrent operations cannot be
reduced to interleaved atomic operations on a single thread), of which
actual hardware is only one example. There are two major approaches to
this problem.

One idea we might have is to augment traces with additional structure,
which we can then quotient away to maintain extensionality by using an
appropriate closure operator. What's nice about this method is that we
can often use structures analogous to the additional state in the
machine model which leads to the relaxed behaviour in the first place.
For example, in #cite(<jagadeesan-brookes-relaxed-12>, form: "prose"),
the authors extend #cite(<brookes-full-abstraction-96>, form: "prose")
with additional state corresponding to the contents of a thread-local
buffer, and then take the closure of their trace-set with respect to
buffer operations such as nondeterministic flushing. This gives them a
model of TSO weak memory with good equational properties and a monadic
structure, which remains intuitive, since it has a connection to the
original TSO model which can also be framed in terms of the abstract
machine having thread-local buffers.
#cite(<release-acquire>, form: "prose") use this approach to derive a
trace-based semantics for release-acquire atomics inspired by their
operational semantics, showing the viability of this technique even for
very complex memory models.

The idea of augmenting traces leads naturally to #emph[games], which we
can view one variant of as sequential traces of moves between a
#emph[proponent] and an #emph[opponent]. Game semantics were first used
with great success to give a semantics to #emph[sequential computation];
for example, #cite(<abramsky-algol-96>, form: "prose") give an adequate
denotational semantics for sequential Algol using Hyland-Ong games
@hyland-ong-00. #cite(<ghica-08>, form: "prose") observe that the
sequentiality of Hyland-Ong games corresponds to a highly constrained,
deterministic form of interleaving between concurrent processes. By
generalizing away many of the rules of Hyland-Ong games, and in
particular #emph[alternation] (i.e., the proponent and the opponent must
take turns), the authors obtain a form of game-semantics for concurrent
programs, which they use to build a fully abstract semantics for
#emph[fine-grained concurrency] (in contrast to
#cite(<brookes-full-abstraction-96>, form: "prose"), which implements
#emph[coarse-grained] concurrency using the somewhat unrealistic
$sans("await")$ primitive).

In general, generalizing traces to represent true concurrency leads us
to another approach: replacing sets of #emph[linear] traces with (sets
of) #emph[partially ordered] structures that directly represent the
concurrency of their component operations. This approach directly
captures the idea that executing two operations concurrently (i.e.,
without specifying an order between them) is fundamentally different
from executing them in some particular order. The most basic such data
structure is a #emph[partially ordered multiset], or #emph[pomset],
which we describe in the TSO weak-memory section of our paper
@ghalayini-24-ssa-densem-arxiv. Pomsets can
naturally model sequential consistency, and, like traces, can be
augmented with additional structure to model relaxed memory models such
as TSO weak memory, as in #cite(<sparky>, form: "prose").

One issue with this approach is that it can be very challenging to
determine the appropriate structures to augment pomsets with in order to
model more advanced memory models. For example,
#cite(<jagadeesan-pwp-20>, form: "prose") introduce #emph[pomsets with
preconditions] (PwP), which augment pomsets with logical formulae, to
model weak memory behaviors. However,
#cite(<leaky-semicolon>, form: "prose") demonstrate that sequential
composition (the semicolon operator) in PwP is not associative. This
lack of associativity undermines many common program optimizations and
breaks the monadic structure necessary for compositional reasoning. To
address this issue, #cite(<leaky-semicolon>, form: "prose") propose
#emph[pomsets with predicate transformers] (PwT), which restore the
associativity of sequential composition. Despite this improvement, their
semantics still do not support loops, and developing a monadic structure
based on PwT that fully supports recursion and iterative constructs
remains future work.

Another potential generalization of pomsets, inspired by game semantics,
is the use of #emph[event structures], which introduce a #emph[conflict
relation] to represent many potentially conflicting executions within a
single mathematical object. #cite(<castellan-16>, form: "prose") show
how to use event structures to represent concurrent executions with
respect to a memory model. They study a simple language supporting
parallel composition of $n$ linear programs defined as lists of loads,
stores, and arithmetic operations, for which event structures provide a
denotational semantics.
#cite(<paviotti-modular-relaxed-dep-20>, form: "prose") use the event
structure approach to give denotational semantics for relaxed memory
concurrency in a more realistic language, including semantics for
branches and loops. However, they employ step indexing in their
semantics, and as a result, loop unrolling is only a refinement rather
than an equation. Since event structures satisfy the axioms of axiomatic
domain theory~@fiore-phd-94, it should be possible to modify this
semantics into one where loop unrolling is an equation, at which point
it would be a model of our calculus.

== Future Work
=== Substructural Types and Effects
#todo[This future-work direction was subsequently developed; preserve the paper wording here and reconcile it with the later refinement chapters during integration.]
Currently, our treatment of effects is relatively primitive, in that,
while we postulate a lattice of effects, our equational theory only
distinguishes between #emph[pure] and #emph[impure] functions, the
former having effect $tack.t$.
#cite(<fuhrmann-direct-1999>, form: "prose") studies languages with
semantics given in an #emph[abstract Kleisli category]. In particular,
he introduces the notion of

- #emph[Central] operations, which commute with all other operations; we
  like to call such morphisms #emph[linear]

- #emph[Duplicable] operations $f$, for which
  $sans("let") y = f(x) ; (y, y) ≈ (f(x), f(x))$

- #emph[Discardable] operations $f$, for which
  $sans("let") y = f(x) ; e ≈ e$ when $e$ does not depend on $y$

While, as we make use of in our calculus, pure operations are central,
duplicable, and discardable, it can be useful to study each notion in
isolation, as well as to consider morphisms which are central and
duplicable (which we have taken to calling #emph[relevant]) and
morphisms which are both central and discardable (which we have taken to
calling #emph[affine]). Examples of morphisms which are not pure but
nonetheless relevant or affine abound; for example,

- In a programming language with nondeterminism, nondeterministic
  functions are #emph[impure] (since $sans("let") y = f(x) ; (y, y)$ is a
  strict refinement of $(f(x), f(x))$), but are
  nontheless #emph[affine], because discarding the result of a
  nondeterministic function does not affect the program's behavior,
  assuming they have no other effect.

- In a programming language with nontermination, nonterminating
  functions with no other effect are impure (since
  $sans("let") y = f(x) ; e$ may diverge even if $e$ does not) but are
  always duplicable, because duplicating a nonterminating function does
  not introduce new effects beyond divergence. Depending on whether the
  language's other effects commute with nontermination, they may in fact
  be relevant.

All three of these concepts still make perfect sense when interpreted
as-is in a Freyd category, and are particularly useful when reasoning
about models of probabilistic programming, such as Markov categories
(which have many affine morphisms) @nlab:markov-category.

Given that such relevant and affine side-effects have substitution
principles which depend on how often a variable is used in a term, we
call such side-effects #emph[substructural]. We might also consider how
we could support substructural, and in particular linear, #emph[types].
Categorically, this corresponds to weakening the requirement that our
base category be cartesian, instead requiring only a symmetric monoidal
category. The resulting generalization of a Freyd category is called an
#emph[effectful category] by #cite(<promonad>, form: "prose").

=== Refinement and Enrichment
#todo[This future-work direction was subsequently developed; preserve the paper wording here and reconcile it with the later refinement chapters during integration.]
Throughout this work, we have focused on the notion of program
#emph[equivalence] $Gamma ⊢ r ≈ r' ▹ sans("L")$. In many
settings, especially when considering the nondeterminism and
concurrency, we would also like to study program #emph[refinement]
$Gamma ⊢ r subset.eq.sq r' ▹ sans("L")$. Semantically, this corresponds to an enrichment of our
model in the category of partial orders; we conjecture that adding this
to our semantics would require minimal changes. We may also consider how
our syntax could be extended to support explicit parallelism and how we
could reflect the corresponding algebraic laws (as given in, e.g.,
#cite(<hoare-parallel-14>, form: "prose")), such as
$(P parallel Q) ; (R parallel S) subset.eq.sq (P ; R) parallel (Q ; S)$
in our equational theory. More generally, we can consider enrichment
with further structures, such as distributive lattices and dcpos, and
the language features these correspond to, such as nondeterministic
choice between programs $P or C$. These features are particularly
interesting from the perspective of programs as #emph[specifications],
as they offer the potential for representing complex specifications
within SSA.

=== Guarded Iteration
Elgot categories and monads were introduced in
#cite(<elgot-elgot-75>, form: "prose"), and subsequently formalized in
#cite(<adamek-elgot-11>, form: "prose").
#cite(<coinductive-resumption-levy-goncharov-19>, form: "prose")
generalize Elgot categories to #emph[guarded Elgot categories] (and,
correspondingly, #emph[guarded Elgot monads], whose Kleisli categories
are guarded Elgot), to support partial non-unique iteration -- in other
words, categories where the fixed point does not always exist.
Generalizing our language with support for guarded iteration could allow
us to study applications of SSA to domains for which not all fixpoints
exist, such as the representation of terminating languages (as, for
example, one would find in a proof assistant) or productive processes.

#cite(<goncharov-metalang-21>, form: "prose") introduce a metalanguage
for guarded iteration based on labelled iteration as presented by
#cite(<geron-iteration-16>, form: "prose"). Interestingly, they refer
to the labels in their systems as #emph[exceptions], making the claim
that this more closely matches their semantics. Similar to our work,
they provide a denotational semantics for this language using the
Kleisli category of a strong guarded #emph[pre-iterative] monad
$bold(T)$---that is, a monad with a guarded fixpoint operator---on a
distributive category $cal(C)$. They then demonstrate that this
semantics is sound and adequate with respect to a big-step operational
semantics for a specific monad, namely
$sans("T") X = (X times bb(N)^ast) + bb(N)^omega$
over $sans("Set")$. Notably, unlike our trace monad, their monad is
#emph[guarded iterative] rather than merely iterative. The infinite
branch of the coproduct $bb(N)^omega$ represents an infinite sequence of
natural numbers, effectively prohibiting non-productive infinite loops
--- that is, recursion that does not pass through a #emph[guard], which
in this context is emitting a natural number. Their treatment of
iteration is thus somewhat more general than ours, as they support
guarded iteration and require only a pre-iterative monad. However, they
focus on Kleisli categories rather than providing a general treatment
for Freyd categories. Additionally, their language supports functional
types, whereas our language is purely first-order. We are very
interested in exploring the connection between guarded
labelled-iteration and SSA implied by the similarities between our
respective syntaxes and semantics.

== Acknowledgements
This work was supported in part by a European Research Council (ERC)
Consolidator Grant for the project "TypeFoundry", funded under the
European Union's Horizon 2020 Framework Programme (grant agreement no.
101002277).
