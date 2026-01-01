= Introduction

/*

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

#todo[
  maybe: explain what a compiler is at a high-level because the intro both sets the tone and pads
  wordcount
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
- Like programming languages, they are designed to be read and written, rather than executed, but
- Like executable code, they are designed to be processed by _machines_, rather than people

A good IR is _simple_: it has a few features which compose well in a predictable manner.
This makes it
- Easy to _generate_ from high-level source code
- Easy to _lower_ to low-level executable code
- Easy to _analyze_ to determine both properties of programs and program equivalence

In particular, a good intermediate representation should be _regular_, in both colloquial senses:
- It should have few to no edge cases in the interpretation of its constructs
- Equivalent programs should map to similar, or preferably the same, IR, as much as possible

To achieve this, we want our IR to have rigorous _invariants_: for example, we might require
- Operations have only pure expressions as arguments, or even
- Operations have only variables or constants as arguments (yielding _A-normal form_, or _ANF_)
- Loops always take canonical, structured forms
  (this is always possible due to the Böhm-Jacopini theorem @bohm-66-structured)

Invariants make both analysis and lowering much easier to reason about and implement, since
there are both fewer cases to consider
and, when considering each case, we have more assumptions to work with.
//
However, this is a double-edged sword:
the more invariants we have, the more difficult it is both to
_generate_ our intermediate representation
and, if we've discovered an optimization opportunity, to _rewrite_ it while preserving invariants.
For example, six of the 13 most invoked passes in the LLVM compiler are spent
discovering and restoring invariants such as SSA or canonical loop forms @reissmann-19-rvsdg.

/*
#scaffold[
  - It is generally accepted that IRs are useful
  - It is generally accepted that SSA is the "standard" IR,
    and many other IRs are variants and dialects of SSA

  Usually, though:
  - Study of IRs, including SSA, is _informal_ and based on engineering practice
    without any rigorous mathematical model for correctness

  So we want to argue:
  - IRs need a _formal_ semantics to:
    - _Verify_ optimizations are correct
    - Provide a _framework_ for
      - Developing new optimizations (IR $=>$ IR)
      - Generalizing optimizations across different platforms
    - _Verify_ the _relationships_ between
      - Different IRs
      - Source languages and IRs
      - IRs and target languages
  - We provide a formal semantics for SSA because:
    - SSA is the canonical IR, and _therefore_
    - A semantics for SSA can be used to provide semantics for _other_ imperative IRs
    - And all these semantic models can be rigorously proven _equivalent_
    - Giving us a theory of categorical imperative programming (title drop)
]

#block-note[
  - _Specific_ intermediate representations each strike a different balance between
    simplicity and regularity (via invariants)
    - A smaller IR is often both simpler and more regular, but
    - More invariants $=>$ less simple, _so_ harder to generate and rewrite
    - Less invariants $=>$ more simple, _but_ harder to analyze and optimize

  - In general, a compiler looks like
    $
      ms("MyCompiler") : ms("Language")_1 => ms("Language")_2
    $
    while preserving, or rather _refining_, semantics.

    An _optimizer_ is therefore a special case which looks like
    $
      ms("MyOptimizer") : ms("Language") => ms("Language")
    $

    Here, the language is usually an IR.

    An optimizer might more specifically _read_ the input IR (_analysis_) and then, as necessary,
    _rewrite_ parts of the input IR (_rewriting_ or _transformation_) based on the results of the
    analysis. So while we model it as a function from IR to IR, in implementation, it is actually
    a mutable imperative rewriter on the IR _data structure_.

    So an _optimizing compiler_ with a single IR in the middle might look like

    $
      ms("MyOC") : ms("Source")
        =>^ms("Generation") ms("IR")
        =>^ms("Optimization") ms("IR")
        =>^ms("Lowering") ms("Target")
    $

    A real compiler often uses _multiple_ IRs each with specialized optimization and analysis
    functions.

    So notice:
    - _Simplicity_ generally makes things easier to _write_. So if $ms("IR")$ is simple:
      - $ms("Generation")$ is easier since we write $ms("IR")$
      - _Rewriting_ is easier since we already know what we need to do
        (by analysis, reading the IR)
        and it's easy to generate valid IR
    - _Regularity_ generally makes this easier to _read_. So if $ms("IR")$ is regular:
      - $ms("Lowering")$ is easier since we read $ms("IR")$
      - _Analysis_ is easier since we can make more assumptions about the IR
        and hence consider fewer edge cases.

        Note even a very simple language can have many edge cases in _analysis_,
        even (in fact _especially_) if it has few edge cases in its _definition_.

    This is precisely why we need an $ms("IR")$,
    because both these goals are orthogonal to the usual goals of both
    programming language design and
    executable language design.

    Executable languages are rarely either regular or simple:
    they have lots of flexibility and edge cases
    to take advantage of the unique features of a given processor's architecutre and
    extract maximum performance.

    Likewise, programming languages need to be simple and regular to _humans_,
    but this is often very different from mathematical simplicity and regularity.
    Humans find it very convenient, for example,
    to be able to write both `x.find()` and `find(x)` depending on what type of function `find` is,
    and this extra context makes things more readable.
    It's now also double the effort writing a compiler, since we've got two cases instead of one.
    So we want to normalize everything
    to the standard `find(x)` form as early as possible to avoid duplicating work.

    Notice, this is totally separate from optimization:
    the two programs have essentially the _same_ performance characteristics, size, and complexity.
    This is about _regularity_ and _simplicity_:
    by enforcing everything be in a normal form,
    a program operating on IR has to deal with fewer cases.
    This is essentially a proof by induction, and we want as few base cases as possible.

    A good programming language focuses on making things readable,
    which often requires making things _short_.

    An IR on the other hand should be _maximally explicit_
    even if no one would ever want to type the entire program,
    for the exact same reason:
    it's much easier for a machine to reason about a fully explicit expression,
    since we don't need to take as much context into account.

    As an example,
    a source language might have an expression with type-dependent meaning,
    like `a + b`.
    - If `a, b` are integers, `a + b` means `addInt a b`
    - If `a, b` are floats, `a + b` means `addFloat a b`
    - If `a, b` are strings, `a + b` means `concatString a b`

    Having an IR reason about `+` is a pain, since we both:
    - Need to do cases on type information when rewriting `+`
    - Have an additional case in our expression language itself, namely the `+` case

    Lowering everything to fully explicit typed functions right at the beginning is hence
    almost universally applied in compiler design.
]

#scaffold[
  - But it also has lots of _invariants_, making it easy to _analyze_ and _rewrite_ while preserving soundness
    - Talk about analysis passes and dataflow
      - Classical IRs are _very good at this_, but they're often underspecified because of imperativity, see: simulation arguments
    - Talk about _optimization passes_
      - Easy to generate code with correct semantics
        - And, very importantly, easy to _inline_: meaning _compositional_
          - High-level languages often make inlining _hard_ because the normies don't prove substitution
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
*/

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

*/

= Concrete Lore

/*
#todo[rewrite this]

We can think of a concrete category $cal(V)$ as "sets with extra structure":

- Each object $A ∈ |cal(V)|$ corresponds to a set $U A$; in particular,
  we will write $a ∈ A$ to mean $a ∈ U A$
- Each morphism $f : cal(V)(A, B)$ corresponds to a _unique_ function $U f : U A → U B$.

  In particular, since $U$ is faithful,
  we can ask whether an arbitrary function $g : U A → U B$
  "is a $cal(V)$-morphism from $A$ to $B$";
  i.e., whether there exists $f : cal(V)(A, B)$ such that $U f = g$.
  If there exists such an $f$, it is unique;
  hence, we can identify the morphisms $cal(V)(A, B)$
  with the subset of functions $U A → U B$ which "are $cal(V)(A, B)$ morphisms."

  In general, we will write such an $f$ if it exists as $U^(-1)_(cal(V)(A, B)) g$.

  We hence justify the further abuse of notation and write

  - $f : A → B$ to mean $U f : U A → U B$ where this would not cause confusion, and, in particular

  - Given $a ∈ A$, we define $f(a) ∈ B$ to mean $(U f)(a) ∈ U B$

As a concrete example, consider the category of partially-ordered sets and monotone functions $ms("Pos")$.
An object of $ms("Pos")$ is a partially-ordered set $(X, scripts(≤)_X)$,
and a morphism $f: (X, scripts(≤)_X) → (Y, scripts(≤)_Y)$ is a monotone function $f : X → Y$, i.e.
a function $f$ such that
$
  ∀ x_1, x_2 ∈ X . (x_1 scripts(≤)_X x_2) ==> (f(x_1) scripts(≤)_Y f(x_2))
$

We can directly equip $ms("Pos")$ with the structure of a concrete category by taking
$U(X, scripts(≤)_X) = X$ and $U f = f$.
Our abuse of notation is then precisely the usual mathematical convention of, for example,
specifying "a monotone function $f : ℕ → pset(X)$" without explicitly specifying that
$ℕ$ is ordered with the usual $≤$ relation on the naturals and
$pset(X)$ is ordered with the subset relation $⊆$.


Another particularly import example is the category of sets $cset$, which is trivially a
concrete category by taking $U$ to be the identity functor.
*/

/*
For the rest of this section, we will develop the theory of $cal(V)$-enriched categories in the
special case where $cal(V)$ is concretely cartesian. The general theory of enriched categories is
analogous, but much more complex since we need to deal with coherence conditions, however,
when $cal(V)$ is concretely cartesian, the definitions are essentially the same as in ordinary
category theory. In fact, we can recover the standard category theoretic definitions by noting that
a category is precisely a $cset$-enriched category.
*/


/*

== Compiling Between #iter-calc() and SSA

#todo[this]

=== Compiling #iter-calc() to SSA

#todo[this]

=== Compiling SSA to #iter-calc()

#todo[this]

== Dialects and Lowerings

#todo[expression-language hom w.r.t. refinement theory]

#todo[a _lowering_ is a refinement-preserving expression-language hom]

#todo[an _optimization_ is a refining endomorphism]

#todo[versus, an automorphism like the #iter-calc() equivalences...]

#todo[#iter-calc(expr2fun(iter-calc(ms("F")))) ≈ #iter-calc(ms("F"))]

*/

= Appendix stuff


= Type Theory

/*
TODO: shunt proof to appendix

#block-note[
  If $sle(ms("X"))$ is a preorder, so is $tyle(ms("X"))$.

  - Reflexivity: if $sty(X)$ is reflexive;
    given $A ∈ sty(ms("X"))$, prove $tywk(A, A)$.

    By induction on type $A$
    - (base): $tywk(X, X)$ (by reflexivity of $sle(ms("X"))$)
    - ($Π$ empty): $tywk(Π [], Π [])$
    - ($Σ$ empty): $tywk(Σ [], Σ [])$
    - ($Π$ cons):
      $tywk(Π lb("T"), Π lb("T"))$ and $tywk(A, A)$ so
      $tywk(Π (lb("T"), fty(lb("f"), A)), Π (lb("T"), fty(lb("f"), A)))$
    - ($Σ$ cons):
      $tywk(Σ lb("T"), Σ lb("T"))$ and $tywk(A, A)$ so
      $tywk(Σ (lb("T"), fty(lb("f"), A)), Σ (lb("T"), fty(lb("f"), A)))$
  - Transitivity: if $sle(ms("X"))$ is transitive;
    given $tywk(A_1, A_2)$ and $tywk(A_2, A_3)$ prove $tywk(A_1, A_3)$.

    Suffices to show $∀ A_3 . tywk(A_2, A_3) => tywk(A_1, A_3)$
    by induction on the derivation $tywk(A_1, A_2)$.

    - @twk-base:
      Have $A_1 = X_1 ∈ ms("X")$, $A_2 = X_2 ∈ ms("X")$
      with $X_1 sle(X) X_2$.

      Fix $A_3$ s.t. $tywk(A_2, A_3)$.
      By inversion on $tywk(X_2, A_3)$, either:
      - $A_3 = X_3 ∈ ms("X")$ with $X_2 sle(X) X_3$;
        in which case result follows by transitivity of $sle(X)$
      - $A_3 = tunit$;
        in which case result follows by @twk-unit.

    - @twk-sigma:
      Have $A_1 = Σ (lb("T")_1, fty(lb("f"), B_1))$, $A_2 = Σ (lb("T")_2, fty(lb("f"), B_2))$
      with $tywk(Σ lb("T")_1, Σ lb("T")_2)$ and $tywk(B_1, B_2)$.

      Fix $A_3$ s.t. $tywk(A_2, A_3)$.
      By inversion on $tywk(Σ (lb("T")_2, fty(lb("f"), B_2)), A_3)$, either:
      - @twk-sigma : $A_3 = Σ (lb("T")_3, fty(lb("f"), B_3))$ with
        $tywk(Σ lb("T")_2, Σ lb("T")_3)$ and $tywk(B_2, B_3)$;

        By induction, have $Σ lb("T")_1 ≤ Σ lb("T")_3$ and $tywk(B_1, B_3)$;
        so result follows by @twk-sigma.

    - @twk-pi:
      Have $A_1 = Π (lb("T")_1, fty(lb("f"), B_1))$, $A_2 = Π (lb("T")_2, fty(lb("f"), B_2))$
      with $tywk(Π lb("T")_1, Π lb("T")_2)$ and $tywk(B_1, B_2)$.

      Fix $A_3$ s.t. $tywk(A_2, A_3)$.
      By inversion on $tywk(Π (lb("T")_2, fty(lb("f"), B_2)), A_3)$, either:
      - $A_3 = Π (lb("T")_3, fty(lb("f"), B_3))$ with
        $tywk(Π lb("T")_2, Π lb("T")_3)$ and $tywk(B_2, B_3)$;

        By induction, have $Π lb("T")_1 ≤ Π lb("T")_3$ and $tywk(B_1, B_3)$;
        so result follows by @twk-pi.

      - $A_3 = tunit$;
        in which case result follows by @twk-unit.

      - @twk-unit : $A_3 = tunit$;
        in which case result follows by @twk-unit.

    - @twk-unit:
      Have $A_2 = tunit$.
      Fix $A_3$ s.t. $tywk(A_2, A_3)$.
      By inversion on $tywk(tunit, A_3)$, $A_3 = tunit$; result follows by @twk-unit.

    - @twk-zero: Have $A_1 = tzero$; result follows by @twk-zero.
]

#block-note[
  If $sle(ms("X"))$ is a partial order, so is $tyle(ms("X"))$

  Suffices to show: if $sle(ms("X"))$ is antisymmetric, so is $tyle(ms("X"))$

  Suffices to show: by induction on $atywk(A, B, ms("X"))$ that $atywk(B, A, ms("X")) => A = B$

  - @twk-base:
    Have $A = X$, $B = Y ∈ ms("X")$ with $X sle(ms("X")) Y$.

    By inversion, result follows from antisymmetry of $sle(ms("X"))$
  - @twk-sigma:
    Have $A = Σ (lb("T"), fty(lb("f"), A'))$, $B = Σ (lb("T"'), fty(lb("f"), B'))$ with
    $atywk(Σ lb("T"), Σ lb("T"'), ms("X"))$ and $atywk(A', B', ms("X"))$.

    By inversion, have $atywk(Σ lb("T"'), Σ lb("T"), ms("X"))$ and $atywk(B', A', ms("X"))$.

    Hence, by induction, have $A' = B'$ and $Σ lb("T") = Σ lb("T"')$;
  - @twk-pi:
    Have $A = Π (lb("T"), fty(lb("f"), A'))$, $B = Π (lb("T"'), fty(lb("f"), B'))$ with
    $atywk(Π lb("T"), Π lb("T"'), ms("X"))$ and $atywk(A', B', ms("X"))$.

    By inversion, have $atywk(Π lb("T"'), Π lb("T"), ms("X"))$ and $atywk(B', A', ms("X"))$.

    Hence, by induction, have $A' = B'$ and $Π lb("T") = Π lb("T"')$;
    implying the desired result.
    implying the desired result.
  - @twk-unit: have $B = tunit$; by inversion, $A = tunit$.
  - @twk-zero: have $A = tzero$; by inversion, $B = tzero$.
]
*/

= Category Theory

//TODO: pull down
/*
#definition(name: "Opposite Category")[
  Given a category $cal(C)$, we define it's opposite category $opc(cal(C))$ to have
  - Objects $|opc(cal(C))| = |cal(C)|$
  - Morphisms $opc(cal(C))(A, B) = { opm(f) | f ∈ cal(C)(B, A) }$
    #footnote[
      This is in bijection with $cal(C)(B, A)$
      // (and is usually defined to be equal to it!)
      but we add the $opm(-)$-tag to avoid confusion.
    ].
  - Composition given by $opm(f) ; opm(g) = opm((g ; f))$
]
*/

/*
In particular:
- The (unique) initial object in $cset$ is the empty set $∅$
- Any singleton set is a terminal object in $cset$.
  We fix a singleton set $tunit_cset = {*}$.
- Likewise, the (unique) initial object in $ms("Cat")$ is the empty category with objects $∅$
- The terminal object in $ms("Cat")$ has
  one object $* ∈ mb(1)_cset$
  and only the identity morphism $id_* : mb(1)_ms("Cat")(*, *)$

#todo[fix this this is not a good discussion]

The existence of the opposite category means that for every structure $cal(S)$
defined on arbitrary categories $cal(C)$,
we can immediately ask whether $cal(S)$ exists on the _opposite category_ $opc(cal(C))$.
If it does, this naturally induces a structure $opc(cal(S))$ on $cal(C)$ as well,
the _dual_ of $cal(S)$.

As an example of this,
- A category $cal(C)$ has an initial object if and only if $opc(cal(C))$ has a terminal object;
  so the terminal object is dual to the initial object
- Likewise, a category $cal(C)$ has a terminal object if and only if $opc(cal(C))$ has an initial object;
  so the initial object is dual to the terminal object
- In general, if $cal(S)$ is dual to $opc(cal(S))$, then $opc(cal(S))$ is dual to $cal(S)$.
  In particular, this means that $opc(opc(cal(S))) = cal(S)$

In general, we get the dual structure $opc(cal(S))$ to $cal(S)$
by flipping the direction of all morphisms in the
definition of $cal(S)$.
*/


/*
#definition(name: [$cal(V)$-Quiver])[
  A $cal(V)$-quiver $cal(Q)$ consists of
  - A set of objects $|cal(Q)|$
  - For each pair of objects $A, B : |cal(Q)|$, a hom-object $cal(Q)(A, B) ∈ |cal(V)|$

  In particular, every $cal(V)$-category can be made into a $cal(V)$-quiver by forgetting
  the identities and composition.

  We define the category of $cal(V)$-quivers $ms("Quiv")_cal(V)$ to have:
  - Objects $cal(V)$-quivers
  - Morphisms $F : ms("Quiv")_cal(V)(cal(Q)_1, cal(Q)_2)$ consisting of
    - A mapping on objects $|F| : |cal(Q)_1| → |cal(Q)_2|$
    - For each pair of objects $A, B : |cal(Q)_1|$, a $cal(V)$-morphism
      $
        F_(A, B) : cal(V)(cal(Q)_1(A, B), cal(Q)_2(F A, F B))
      $
  - Identity morphisms $id_(cal(Q)) = (id, id)$
  - Composition given by
    - $|F ; G| = |G| ∘ |F|$
    - $(F ; G)_(A, B) = F_(A, B) ; G_(F A, F B)$

  In particular, this is the same as composition of functors,
  giving us a faithful forgetful functor from the category of $cal(V)$-categories
  $ms("Cat")_cal(V)$ to the category of $cal(V)$-quivers $ms("Quiv")_cal(V)$.

  Given a family of $cal(V)$-quivers $cal(Q)_i$ for $i ∈ I$, we may define:
  - The _product quiver_ $Π_i Q_i$
]
*/

/*
#definition(name: [$cal(V)$-Multifunctor])[
  Given a family of $cal(V)$-categories $scat(C) = [cal(C)_i | i ∈ I]$
  and a $cal(V)$-category $cal(D)$,
  a _multifunctor_ $F$ from $icol(C)$ to $cal(D)$ consists of
  - A mapping from families of objects $icol(A) = [A_i : |cal(C)_i| | i ∈ I]$
    to objects $F icol(A) : |cal(D)|$
  - For each $j ∈ I$,
    a mapping from families of objects $icol(A)_j = [A_i : |cal(C)_i| | i ∈ I backslash {j}]$
    a $cal(V)$-functor
    $
      F med icol(A)_j : cal(C)_j → cal(D)
    $
    such that
    $
      ∀ A_j : |cal(C)_j|, F_j med icol(A)_j med A_j = F med icol(A) : |cal(D)|
    $
    where
    $
      icol(A) = [j ↦ A_j] ovrd icol(A)_j = [A_i | i ∈ I]
    $

  In other words, $F$ is a function of $A_i$
  which is a $cal(V)$-functor in each argument $A_j$ _separately_,
  when all other arguments $A_i$ for $i ≠ j$ are held fixed.

  Given $cal(V)$-multifunctors $F, G: scat(C) → D$, we say that a family of morphisms
  $η_icol(A): cal(D)(F icol(A), G icol(A))$ is _natural_ in $j ∈ I$ if,
  for each family of objects $icol(A)_j = [A_i : |cal(C)_i| | i ∈ I backslash {j}]$,
  the family of morphisms $η_icol(A)_j$ given by
  $(η_icol(A)_j)_X := η_([j ↦ X] ovrd icol(A)_j)$
  is a natural transformation $η_(icol(A)_j) : F icol(A)_j => G icol(A)_j$.

  That is, for every morphism $f : cal(C)_j (A_j, A_j')$,
  we have that the following diagram commutes
  $
    #diagram(cell-size: 15mm, $
      F med icol(A) edge(η_icol(A), ->) edge("d", F med icol(A)_j med f, ->) &
      G med icol(A) edge("d", G med icol(A)_j med f, ->, label-side: #left) \
      F med icol(A)' edge(η_icol(A)', ->, label-side: #right) & G med icol(A)' $)
  $
  where
  $
    icol(A) = [j ↦ A_j] ovrd icol(A)_j = [A_i | i ∈ I] quad quad quad
    icol(A)' = [j ↦ A_j'] ovrd icol(A)_j = [A_i | i ∈ I]
  $
]
*/

/*
#definition(name: [$cal(V)$-Natural Multitransformation])[
  Given $cal(V)$-multifunctors $F, G: scat(C) → D$, we define a $cal(V)$-natural multitransformation
  $η : F => G$ to consist of:
  - For each family of objects $icol(A) = [A_i : cal(C)_i | i ∈ I]$,
    a morphism $η_(icol(A)) : cal(D)(F icol(A), G icol(A))$
  - For each $j ∈ I$,
    a mapping from families of objects $icol(A)_j = [A_i : cal(C)_i | i ∈ I backslash {j}]$
    a natural tranformation
    $
      η_icol(A)_j : F_j med icol(A)_j => G_j med icol(A)_j
    $
    such that
    $
      ∀ A_j : |cal(C)_j|, (η_(icol(A)_j))_(A_j) = η_[A_i | i ∈ I]
        : cal(D)(F [A_i | i ∈ I]) → cal(D)(G [A_i | i ∈ I])
    $

  In other words, if we consider $F$, $G$, and $η$ as functions of $A_i$, and, for a given $j ∈ I$,
  fix all $A_i$ for $i ≠ j$, then
  - $F$ and $G$ are functors
  - $η$ is a natural transformation from $F$ to $G$

  That is, $η$ is a natural transformation in each argument $A_j$ _separately_,
  i.e., is _natural in $A_j$_.
]
*/

/*
We define a

Consider now families of objects
$X_(A_1,...,A_n), Y_(A_1,...,A_n) ∈ |cal(C)|$ parametrized by $n$ objects $A_i ∈ |cal(C)|$
and a family of morphisms
$m_(A_1,...,A_n) : cal(C)(X_(A_1,...,A_n), Y_(A_1,...,A_n))$.
We say that $m$ is _natural_ in $A_i$ if:
- There exists a $cal(V)$-functor $F_i$ such that
  $F_i med B = X_i$

Given a function $|cal(C)|^n → |cal(C)|$
*/
