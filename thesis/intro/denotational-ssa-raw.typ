// Verbatim mechanical transcription from:
// papers/isotope/denotational-semantics-of-ssa.tex
// Repository commit: afa82558acf643f53a3e038e635ed9520ace88c6
// Source sections: Abstract, lines 223–235; dedication, lines 272–274; Introduction, lines 276–406

#import "/lib/prelude.typ": *
#show: chapter.with(title: "Introduction")

= Abstract

Static single assignment form, or SSA, has been the dominant
compiler intermediate representation for decades. In this paper, we
give a type theory for a variant of SSA, including its equational
theory, which are strong enough to validate a variety of control and
data flow transformations. We also give a categorical semantics for
SSA, and show that the type theory is sound and complete with
respect to the categorical axiomatization. We demonstrate the
utility of our model by exhibiting a variety of concrete models
satisfying our axioms, including in particular a model of TSO weak
memory. The correctness of the syntactic metatheory, as well as the
completeness proof has been mechanized in the Lean proof assistant.

#emph[This paper is dedicated to the memory of Alan Jeffrey, who
taught us about both premonoidal categories and the semantics of weak memory, and
who never shied away from either theory or implementation.]

<introduction>
Static single assignment form, or SSA form, has been the dominant compiler intermediate representation since its introduction by #cite(<alpern-ssa-original-88>, form: "prose") and #cite(<rosen-gvn-1988>, form: "prose") in the late 1980s. Most major compilers -- GCC, Clang, MLIR, Cranelift -- use this representation, because it makes many optimizations much easier to do than traditional 3-address code IRs.

The key idea behind SSA is to adapt an idea from functional programming: namely, every variable is defined only once. This means that substitution is unconditionally valid, without first requiring a dataflow analysis to compute where definitions reach. Furthermore, because variables are immutable, they can have at most one value, which means that a program analysis only needs to store an abstract value once per variable, rather than once per variable per progam point, reducing memory overheads from quadratic to linear. Unlike in functional programming, though, scoping of definitions in SSA is traditionally not lexical. Instead, scoping is defined by #emph[dominance]: every variable occurrence must be dominated by a single assignment in the control flow graph.

Traditionally, the semantics of SSA has been handled informally. Since it was conceived of as a simple first-order imperative programming language, whether a rewrite is sound or not was usually obvious, without needing any complex correctness arguments. Unfortunately, all of computers, languages and compilers have become more complex since the late 1980s.

Essentially all modern computers are multicore and feature many levels of caching. As a result, the semantics of memory can no longer be correctly modelled as a big array of bytes, and the execution of a multithreaded program can no longer be viewed as an interleaving of its threads' sequential execution traces. Finding good semantics for modern weak memory systems remains an ongoing challenge. Furthermore, each programming language's semantics must also have its own model of weak memory which both abstracts over the differing weak memory models of all the architectures the language gets compiled to, and also validates the optimizations which compiler writers wish to perform. Finally, modern compilers exploit semantic properties like undefined behaviour to transform programs much more aggressively than they did in the previous millenium.

As a result, it is no longer correct to justify compiler optimizations in terms of the simple imperative model, and it is an open question which equations should hold of an SSA program. Note that the pressure on SSA as an intermediate representation comes from all directions: the machine semantics, the language semantics, and the compiler optimizations have all become more complicated. Once all of these concerns are tangled together, it is very hard to decide if a particular transformation should hold or not.

To resolve this issue, we propose studying the equational theory of SSA. Having a well-defined equational theory for SSA will let us disentangle these concerns, because the equational theory can serve as an interface which both compiler writers and hardware designers can use. The compiler writers can rely upon the equational theory of SSA when justifying optimizations, without needing to know all the details of the memory model at all times. Conversely, memory models could be validated by seeing if they satisfy the equations of SSA, without needing to study every possible compiler optimization.

Defining an equational theory for SSA is a nontrivial problem, for both minor and major reasons. Traditionally, SSA is presented as a collection of basic blocks augmented with $phi.alt$-functions to handle control-flow merges. This is a good representation for compiler engineering, but creates a large number of papercuts when defining an operational semantics or equational theory. Operational semantics for SSA have to keep track of the execution history to correctly interpret $phi.alt$-nodes, and the lack of compound expressions makes it awkward to define and use primitives like parallel substitution. In addition, when all one has is an operational semantics, the only natural notion of program equivalence is contextual equivalence. Unfortunately, contextual equivalence is extremely sensitive to the effects available in the language (and SSA often has to deal with very complex effects like weak memory), and this makes it difficult to formulate a criterion for when the equational theory is complete.

If we had a class of denotational models for SSA, then it would be possible to give an equational theory, and show that it is complete (or not) relative to this class of models. But this is precisely the classical methodology of type theory and categorical logic! To fully understand a programming language, in general one wants a type theory equipped with an equational theory, a proof that it is sound and complete with respect to a categorical axiomatization, and a variety of interesting concrete models satisfying those axioms. Moreover, it would be best if the categorical axiomatization was constructed from "standard parts": the less novel the categorical axioms, the better, because standard constructions are better-studied and have more theorems already proved about them. This is exactly what we provide in this paper. Concretely, our contributions are as follows:

- First, we give a type-theoretic presentation of SSA, with both typing rules (in Section~#todo[Cross-reference: \@sec:typing]) and an equational theory (in Section~#todo[Cross-reference: \@sec:equations]) for well-typed terms. We also prove the correctness of suitable substitution properties for this calculus.

- Next, in Section~#todo[Cross-reference: \@sec:densem], we give a categorical semantics for this type theory, in terms of distributive Elgot categories, which are Freyd categories equipped with distributive coproducts and a strong Conway iteration operator. This demonstrates that a categorical semantics for SSA can be constructed from well-known structures. We use Freyd categories to model sequencing of imperative computations, we use coproducts to model conditionals, and we use Conway iteration to model looping.

  We show that any category with this structure is a model of SSA. This establishes that all of the equations we give are sound with respect to the categorical structure.

- We also show, in Section~#todo[Cross-reference: \@ssec:completeness], that syntax quotiented by the equational theory yields the initial distributive Elgot category. This establishes that our set of syntactic equations is complete, and that there are no equations which the denotational semantics validates, but which cannot be proved syntactically.

  Theoretically, this leads us to the surprising discovery that SSA is actually a syntactic presentation of distributive Elgot categories, thereby establishing a surprising connection between compiler IRs and category theory. (In fact, our calculus is also the first syntactic presentation of distributive Elgot categories.)

  Practically, it means that we can freely mix equational and semantic reasoning depending on what is convenient for the problem at hand: a semantic proof which holds in all $lambda_(sans("SSA"))$-models guarantees the existence of a corresponding syntactic sequence of rewrites.

- We proceed in Section~#todo[Cross-reference: \@sec:concrete] to show that this denotational axiomatization is useful in practice. We give a model of TSO weak memory based on~#cite(<sparky>, form: "prose") in Section~#todo[Cross-reference: \@ssec:tso], We also give a family of concrete models based on Brookes-style traces~@brookes-full-abstraction-96, which can be instantiated to support the release/acquire model of~#cite(<release-acquire>, form: "prose"). This demonstrates that it is possible to give realistic weak memory models, in a variety of semantic styles, which do not disturb the structure of SSA in fundamental ways. Furthermore, our results constitute the first proof that SSA-based loop transformations are compatible with weak memory.

- Finally, we have substantially mechanized our proofs using the Lean 4 proof assistant. We have mechanized proofs of substitution for our type theory, as well as proofs that the syntax forms the initial model, and that the SPARC TSO semantics forms a valid model of SSA. The denotational semantics and its proof of the soundness of substitution are done on paper.
