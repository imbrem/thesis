#import "@preview/simplebnf:0.1.1": *
#import "@preview/subpar:0.2.2"

#import "@preview/wordometer:0.1.5": word-count
#show: word-count.with(exclude: (<no-wc>, <appendix>))

#let production = false;

#import "thesis-template.typ": *
#import "todos.typ": *

#import "syntax.typ": *

#show: show-syntax

#show ref: it => {
  let el = it.element
  if el == none or el.func() != figure {
    it
  } else {
    link(el.location(), el.supplement)
  }
}

// TODO: think of a better way to go fix ∅...
// #show math.equation: set text(font: "STIX Two Math")

#set text(lang: "en")

#set heading(numbering: "1.")

#show heading.where(level: 0): set heading(supplement: [Chapter])

#set document(
  title: [
    Categorical imperative programming
    //: type theory, refinement, and semantics for SSA
  ],
  author: "Jad-Elkhaleq Ghalayini",
  date: datetime(day: 12, month: 1, year: 2026),
)

#align(center + horizon)[
  #title()

  *Type theory, refinement, and semantics for SSA*

  \

  \

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

#(thesis-state.update)(body-state)

= Introduction

#todo[
  TFW I need a thesis statement
]

#todo[
  Thesis Map:

  - What is SSA? > @chap-ssa
  - Background, conventions, and notation > @background
  - Type theory, equivalence, and refinement > @ssa-type
  - Semantics of SSA > @ssa-semantics
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

= Static Single Assignment (SSA) <chap-ssa>

== From RTL to SSA

#todo[still need a note about $(V)$]

#todo[
  when I say indexed family, I mean
  - a family over $I$. only ordered if $I$ is canonically ordered
  - in particular, lists are actually pairs $(n ↦ a)$ with standard order on $n ∈ ℕ$
]

#todo[
  If we manage to prove lattice substitution, remove label-set annotations
]

#todo[RTL text]

#figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 1em),
      bnf(
        Prod($o$, {
          Or[$v$][_value_]
          Or[$f med v$][_app_]
          Or[$lb("l")$][_label_]
          Or[$lb("f") med v$][_field_]
        }),
        Prod($v$, {
          Or[$x$][_variable_]
          Or[$(V)$][_structure_]
        }),
        Prod($V$, {
          Or[$·$][]
          Or[$V, fexpr(lb("f"), x)$][]
        }),
      ),
      bnf(
        Prod($β$, {
          Or[$x = o seq β$][_assign_]
          Or[$τ$][_terminator_]
        }),
        Prod($τ$, {
          Or[$retb(o)$][_return_]
          Or[$brb(lb("l"))$][_branch_]
          Or[$sswitch(o, K)$][_switch_]
        }),
        Prod($K$, {
          Or[$·$][]
          Or[$K, ssbr(lb("l₁"), retb(o))$][_return_]
          Or[$K, ssbr(lb("l₁"), brb(lb("l₂")))$][_branch_]
        }),
      ),
      bnf(Prod($G$, {
        Or[$β$][]
        Or[$G seq lb("l") : β$][]
      })),
    )
    $
      (x_0,...,x_(n - 1)) = (x_i)_(i ∈ 0..n-1)
      := (fexpr(π_0, x_0),..., fexpr(π_(n - 1), x_(n - 1)))
      quad
      "where"
      quad
      lpi = π_0,
      rpi = π_1
    $
  ],
  caption: [
    Grammar for #rtl-flat()

    /*
    #block-note[
      Here, $G$ is not always a valid graph, because a label may point to more than one basic block.
      Once we _typecheck_ our syntax, this case, and numerous other mistakes (e.g. adding an integer
      to a string) are statically ruled out, leaving us only with well-formed RTL programs we can
      assign a meaning to.
    ]
    */
  ],
  kind: image,
) <rtl-grammar>

#todo[text]

#subpar.grid(
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

#todo[text]

#subpar.grid(
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
      As #rtl-flat() \ \
    ],
  ),
  <rtl-factorial>,

  columns: (1fr, 1fr),
  caption: [
    A simple, slightly suboptimal program to compute 10! via multiplication in a loop,
    represented as typical imperative code and in #rtl-flat().
  ],
)

#figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 1em),
      bnf(
        Prod($o$, {
          Or[$v$][_value_]
          Or[$f med v$][_app_]
          Or[$lb("l") med v$][_label_]
          Or[$lb("f") med v$][_field_]
        }),
        Prod($v$, {
          Or[$x$][_variable_]
          Or[$(V)$][_structure_]
        }),
        Prod($V$, {
          Or[$·$][]
          Or[$V, fexpr(lb("f"), x)$][]
        }),
      ),
      bnf(
        Prod($β$, {
          Or[$x = o seq β$][_assign_]
          Or[$τ$][_terminator_]
        }),

        Prod($τ$, {
          Or[$brb(lb("l"), o)$][_branch_]
          Or[$scase(o, K)$][_case_]
        }),
        Prod($K$, {
          Or[$·$][]
          Or[$K, sbr(lb("l₁"), x, brb(lb("l₂"), o))$][]
        }),
      ),
      bnf(
        Prod($G$, {
          Or[$β$][]
          Or[$G seq gbr(lb("l"), x, β)$][]
        }),
      ),
    )
  ],
  caption: [
    Grammar for (basic-blocks-with-arguments) #ssa-a-flat().
  ],
  kind: image,
) <bba-grammar>

== Lexical SSA

#figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 1em),
      bnf(
        Prod($o$, {
          Or[$v$][_value_]
          Or[$f med v$][_application_]
          Or[$lb("l") med v$][_label_]
          Or[$lb("f") med v$][_field_]
        }),
        Prod($v$, {
          Or[$x$][_variable_]
          Or[$(V)$][_structure_]
        }),
        Prod($V$, {
          Or[$·$][]
          Or[$V, fexpr(lb("f"), x)$][]
        }),
      ),
      bnf(
        Prod($r$, {
          Or[$x = o seq r$][_assign_]
          Or[$(V) = o seq r$][_destructure_]
          Or[$τ seq L$][_terminator_]
        }),
        Prod($τ$, {
          Or[$brb(lb("l"), o)$][_branch_]
          Or[$scase(o, K)$][_case_]
        }),
        Prod($K$, {
          Or[$·$][]
          Or[$K, sbr(lb("l₁"), x, brb(lb("l₂"), o))$][]
        }),
      ),
    )
  ],
  caption: [
    Grammar for lexical SSA (#ssa-calc())
  ],
  kind: image,
) <lex-ssa-grammar>

== Expressions and Substitution

#figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (4em, 0em),
      bnf(
        Prod(
          $e$,
          {
            Or[$x$][_variable_]
            Or[$f med e$][_app_]
            Or[$lb("l") med e$][_label_]
            Or[$lb("f") med e$][_field_]
            Or[$(E)$][_structure_]
            Or[$elet(x, e_1, e_2)$][_let-binding_]
            Or[$ecase(e, M)$][_cases_]
            Or[$eiter(e_1, x, e_2)$][_iteration_]
          },
        ),
      ),
      bnf(
        Prod(
          $E$,
          {
            Or[$·$][_nil_]
            Or[$E, fexpr(lb("f"), e)$][_cons_]
          },
        ),
        Prod(
          $K$,
          {
            Or[$·$][_nil_]
            Or[$M seq ebr(lb("l"), x, a)$][_cons_]
          },
        ),
      ),
    )
  ],
  caption: [
    Grammar for #iter-calc()
  ],
  kind: image,
) <iter-calc-grammar>

#figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 2em),
      bnf(
        Prod($r$, {
          Or[$x = e seq r$][_assign_]
          Or[$τ seq L$][_terminator_]
        }),
        Prod($L$, {
          Or[$·$][]
          Or[$L seq gbr(lb("l"), x, {r})$][]
        }),
      ),

      bnf(
        Prod($τ$, {
          Or[$brb(lb("l"), e)$][_branch_]
          Or[$scase(e, B)$][_case_]
        }),
        Prod($B$, {
          Or[$·$][]
          Or[$B, sbr(lb("l₁"), x, brb(lb("l₂"), e))$][]
        }),
      ),
    )
  ],
  caption: [
    Grammar for lexical SSA with expressions (#ssa-calc(iter-calc()))
  ],
  kind: image,
) <lex-ssa-e-grammar>


== Type-Theoretic SSA

#figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 1em),
      bnf(Prod($r$, {
        Or[$x = e seq r$][_assign_]
        Or[$brb(lb("l"), e)$][_branch_]
        Or[$scase(e, L)$][_case_]
        Or[${ r } seq L$][_braces_]
      })),
      bnf(
        Prod($L$, {
          Or[$·$][]
          Or[$gbr(lb("l"), x, {r}) seq L$][]
        }),
      ),
    )
    \
  ],
  caption: [
    Grammar for type-theoretic SSA with expressions (#gssa-calc(iter-calc()))
  ],
  kind: image,
) <tt-ssa-grammar>

= Background <background>

#todo[
  Add a map here:
  - Foundations:
    - Grothendieck-Tarski set theory
    - Formalizations in Lean 4 (≈ intuitionistic MLTT variant w/ universe hierarchy)
  - Basic data structure notations:
    - Conventions: zero-indexing, Perl-like duck typing (lists are ℕ-indexed families), etc.
    - Families, reindexings, sequences, and lists
    - Section on basic syntax/grammar? _Probably_ not...
  - Categorical basics?
    - Move up commutative diagrams, functors, natural transformations?
    - Products + terminal here? Coproducts / initial?
    - Monads here? Relate to computational monads? Definitely need products...
    - Sketch:
      - Categories and diagrams
      - Functors and natural transformations
      - Natural isomorphisms; equivalence of categories vs. isomorphism of categories
      - Opposite cateogry, _contravariant_ functors, duality
      - Products, terminal object
      - LEVEL 2: CCCs and exponentials
        - LEARNING: what is a coexponential?
      - Coproducts, initial object
      - Monads
        - Preserve coproducts
          - LEARNING: any exact conditions here? Tfw "works in #cset"
        - Can be _strong_ w.r.t. product structure
        - Can be _commutative_ w.r.t. themselves
        - Have a standard presentation in #cset via pure/bind
          - LEARNING:
            How general is the standard presentation? Do we need additional structure over a CCC?
      - Concrete categories
        - Concrete (functors)
        - Concretely cartesian (functors)
        - LEVEL 2: CCCC (functors) from @adamek-09-cats
]

#todo[
  The idea:
  - Background knowledge up here; skippable. Need a better title than "Conventions and Notation".
    Perhaps even "Background"?
  - Then: type theory. As cats are pre-developed, light mentions are OK, and nothing is enriched.
  - Then:
  - Then: category theory
    - Rapidly develop everything _again_ in the $cal(V)$-enriched setting, so no _true_ duplication
    - Second explanation focuses on computational intuition
      - First explanation (here) focuses on categorical intuition
  - Then: basic models in category theory
  - Then: concrete models

  - LEVEL 3: _substructural_ models of #iter-calc(), associated lore
]

#[
  == Conventions and Notation
  #set heading(offset: 2)
  #include "content/background/conventions.typ"
]

#[
  #set heading(offset: 1)
  #include "content/background/category-theory.typ"
]

= Type Theory <ssa-type>

== Typing Rules

=== Types and Contexts

#todo[introduce types]

#figure(
  [
    #grid(
      align: left,
      columns: 2,
      gutter: (2em, 2em),
      bnf(
        Prod($A$, {
          Or[$tybase(X)$][_base type_ $X ∈ ms("X")$]
          Or[$Σ lb("L")$][_Σ (coproduct)_]
          Or[$Π lb("T")$][_Π (product)_]
        }),
      ),
      bnf(
        Prod($lb("L")$, {
          Or[$·$][]
          Or[$lb("L"), lty(lb("l"), A)$][]
        }),
        Prod($lb("T")$, {
          Or[$·$][]
          Or[$lb("T"), fty(lb("f"), A)$][]
        }),
      ),
    )
    $
      A × B & := Π ( kwl : A, kwr : B ) & #h(3em) & mb(1) & := Π (·) \
      A + B & := Σ ( kwl(A), kwr(B) )   &         & mb(0) & := Σ (·)
    $
    $
      Π [A_0,...,A_(n - 1)] & = Π_i A_i & := Π ( lb("p")_0 : A_0, ..., lb("p")_(n - 1) : A_(n - 1) ) \
      Σ [A_0,...,A_(n - 1)] & = Σ_i A_i &   := Σ ( lb("i")_0(A_0), ..., lb("i")_(n - 1)(A_(n - 1)) )
    $
    \
  ],
  caption: [Grammar for simple types parametrized by base types $ms("X")$],
  kind: image,
)

#todo[
  We treat $lb("L"), lb("T")$ as _label-indexed families_, quotiented by order

  For example, we could sort by labels, and assume no duplicates.

  Note on the locally-nameless trick
]

#todo[introduce _weakening_ of types]

#import "content/rules/twk.typ": *

#fig-r-twk

#lemma[
  If $sle(ms("X"))$ is a partial order, so is $tyle(ms("X"))$
]

#todo[Has joins when $ms("X")$ has _bounded_ joins]

#todo[Has meets when $ms("X")$ has _bounded_ meets]

#figure(
  [
    $
      X ⊔_(sty(ms("X"))) Y = cases(X ⊔_X Y "if defined", tunit "otherwise")
      quad quad quad
      X ⊓_(sty(ms("X"))) Y = cases(X ⊓_X Y "if defined", tzero "otherwise")
      \
      A ⊔ tunit = tunit ⊔ A = tunit quad quad
      A ⊔ tzero = tzero ⊔ A = A quad quad
      A ⊓ tunit = tunit ⊓ A = A quad quad
      A ⊓ tzero = tzero ⊓ A = tzero
    $
    $
      Σ lb("L") ⊔ Σ lb("L'") & :=
                               Σ (lty(lb("l"), labhi(lb("L"), lb("l")) ⊔ labhi(lb("L"), lb("l")))
                                 | lb("l") ∈ lab(lb("L")) ∪ lab(lb("L"'))) \
      Π lb("T") ⊔ Π lb("T'") & :=
                               Π (fty(lb("l"), fldhi(lb("T"), lb("l")) ⊔ fldhi(lb("X"'), lb("l")))
                                 | lb("l") ∈ fld(lb("T")) ∩ fld(lb("X"'))) \
      Σ lb("L") ⊓ Σ lb("L'") & :=
                               Σ (lty(lb("l"), lablo(lb("L"), lb("l")) ⊓ lablo(lb("L"), lb("l")))
                                 | lb("l") ∈ lab(lb("L")) ∩ lab(lb("L"'))) \
      Π lb("T") ⊓ Π lb("T'") & :=
                               Π (fty(lb("l"), fldlo(lb("T"), lb("l")) ⊓ fldlo(lb("T"), lb("l")))
                                 | lb("l") ∈ fld(lb("T")) ∪ fld(lb("X"')))
    $
    where
    $
      lablo(lb("L"), lb("l")) = cases(
        A "if" lty(lb("l"), A) ∈ lb("L"),
        tzero "otherwise"
      ) quad quad
      labhi(lb("L"), lb("l")) = cases(
        A "if" lty(lb("l"), A) ∈ lb("L"),
        tunit "otherwise"
      )
    $
    $
      fldlo(lb("T"), lb("f")) = cases(
        A "if" fty(lb("f"), A) ∈ lb("T"),
        tzero "otherwise"
      ) quad quad
      fldhi(lb("T"), lb("f")) = cases(
        A "if" fty(lb("f"), A) ∈ lb("T"),
        tunit "otherwise"
      )
    $
    $
      lab(·) = ∅ quad
      lab(lb("L"), lty(lb("l"), A)) = lab(lb("L")) ∪ { lb("l") } quad
      fld(·) = ∅ quad
      fld(lb("T"), fty(lb("f"), A)) = fld(lb("T")) ∪ { lb("f") }
    $

    \
  ],
  caption: [Lattice structure on simple types $sty(ms("X"))$],
)

#todo[Grammar for (label) contexts]

#todo[Should we repeat the rules and such here?]

#todo[
  Contexts over $sty(ms("X"))$ of the form $Γ, ms("L")$ are isomorphic to $lb("T"), lb("L")$;
  "concepts with attitude"
]

#todo[
  not quite the same as distinguishing $lb("T"), lb("L")$, since _these_ have different variance
]

#fig-r-cwk

=== Expressions

#todo[introduce concept of a function space]

#todo[fix notation for function space judgement]

#todo[IMPORTANT: while $Π$-types are unordered, tuples $(E)$ are _ordered_ left-to-right!]

#import "content/rules/hasty.typ": *

#fig-r-hasty

#todo[explain #op-calc(ms("F")), #case-calc(ms("F")) as sublanguages of #iter-calc(ms("F"))]

=== Regions

#todo[introduce concept of an _expression space_]

#todo[fix notation for expression space judgement]

#import "content/rules/haslb.typ": *

#figure(
  [
    #rule-set(
      declare-rule(r-br),
      declare-rule(r-case),
      declare-rule(r-case),
      declare-rule(r-case-nil),
      declare-rule(r-case-cons),
    )
    \
  ],
  caption: [Typing rules for #br-calc(ms("E"))],
)

#todo[introduce concept of a _region space_]

#figure(
  [
    #rule-set(
      declare-rule(r-assign),
      declare-rule(r-tm),
      declare-rule(r-lb-nil),
      declare-rule(r-lb-cons),
    )
    \
  ],
  caption: [Typing rules for #ssa-calc(ms("E"), ms("T"))],
)

#todo[SSA is just a region-space too... hence gSSA]

#todo[_slightly_ adjust grammar; this allows for custom terminators, which is always fun!]

#figure(
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 1em),
      bnf(Prod($r$, {
        Or[$x = e seq r$][_assign_]
        Or[$brb(lb("l"), e)$][_branch_]
        Or[$scase(e, L)$][_case_]
        Or[$τ$][_terminator_]
        Or[${ r } seq L$][_braces_]
      })),
      bnf(
        Prod($L$, {
          Or[$·$][]
          Or[$gbr(lb("l"), x, {r}) seq L$][]
        }),
      ),
    )
    \
  ],
  caption: [Grammar for #gssa-calc(ms("E"), ms("T"))],
  kind: image,
)

#figure(
  [
    #rule-set(
      declare-rule(r-g-assign),
      declare-rule(r-g-br),
      declare-rule(r-g-case),
      declare-rule(r-g-scope),
      declare-rule(r-g-lb-nil),
      declare-rule(r-g-lb-cons),
    )
    \
  ],
  caption: [Typing rules for #gssa-calc(ms("E"), ms("T"))],
)

=== Metatheory

#todo[Weakening; connection to thinning]

#todo[Label weakening]

#todo[Type weakening]

#todo[Implies a lattice of types]

#todo[Typed weakening]

#todo[Implies a lattice of contexts]

#todo[Typed label weakening]

#todo[Implies a lattice of label-contexts]

#todo[Substitution]

== Expressions

#todo[introduce the concept of an _equational theory_ $req$]

#todo[begin with globally valid rewrites?]

#todo[note: 
  _all_ rewrites are globally valid _except_ for:
  - $β$, which needs $ε$ to be:
    - relevant + affine. _intuitionistic_?
    - central w.r.t. $η$
  - 
]

#todo[_elas_ ; we need effects for $β$ and $η$ rules! I always forget $η$ is green...]

#todo[discuss _refinement_ via effects]

=== Effects

#todo[
  introduce the concept of an _effect system_ $cal("E")$;
  for simplicity, want a _bounded partial order_ of effects.

  Effect systems are _always_ linear, because why not?
]

#todo[
  - 
]

#todo[effects and nontermination; introduce the concept of an _iterative_ effect system]

#todo[introduce notion of _direct_ effect]

#fig-r-eff-hasty

#todo[introduce _$β$-rule_]

#todo[introduce _uniformity_]

#todo[actual effect rules are nicer]

#todo[
  we don't start with the actual rules to avoid mutual recursion between effect system
  and equivalence theory
]

#figure(
  [
    #todo[this]
  ],
  caption: [Equivalence rules for #iter-calc(ms("F"))],
)

#fig-r-eq-congr-hasty

=== Linearity

#todo[introduce the concept of a _quantity_; view it as an extension of a type]

#todo[
  introduce the concept of a _linearity system_ $ms("U")$: 
  assigns lattice quantities to base types _and that's it_.
]

#fig-r-utywk

#fig-r-uctxwk

#fig-r-q-hasty

=== Refinement

#todo[
  introduce the concept of a _linear effect system_ $cal(E)$
]

#todo[introduce the concept of a _refinement theory_ $ms("R")$]

#todo[
  note: we don't track effects of duplication/deletion because that would be hard;
  cool for RC but not for us
]

#todo[introduce _directed $β$-rule_]

#todo[introduce _directed uniformity_]

#figure(
  [
    #todo[this] \
  ],
  caption: [Refinement rules for #iter-calc()],
)

#fig-r-ref-congr-hasty

== Regions

#figure(
  [
    #todo[this]
  ],
  caption: [Equivalence rules for #gssa-calc()],
)

#figure(
  [
    #todo[this]
  ],
  caption: [Congruence rules for #gssa-calc() equivalence],
)

=== Effects

#todo[effects for regions is just like for expressions; _except_]

#todo[
  jumping to a label invokes that label's effects;
  so we need to keep track of each label's effects
]

#figure(
  [
    #todo[this]
  ],
  caption: [Effect rules for #gssa-calc()],
)

=== Linearity

#todo[likewise, linearity is the same...]

#todo[except that we need to track usage information across labels...]

#todo[
  which means tracking usage/type information across labels too;
  so we need an _extended label context_
]

#todo[
  this gets a judgement which is irritating, but routine;
  it's just pointwise weakening.

  Can allow synthesis across branches due to locally nameless lore.
]

#figure(
  [
    #todo[this]
  ],
  caption: [Linearity rules for #gssa-calc()],
)

=== Refinement

#figure(
  [
    #todo[this]
  ],
  caption: [Refinement rules for #gssa-calc()],
)

#figure(
  [
    #todo[this]
  ],
  caption: [Congruence rules for #gssa-calc() refinement],
)

= Semantics of SSA <ssa-semantics>

#todo[
  Chapter structure:
  - We introduce some category theory.
    The goal is a _$cal(V)$-enriched distributive copy-discard Elgot category_.
  - Each _enriched structure_ corresponds to some form of _control_:
    - Categories: sequential control-flow
    - Coproducts: branching control-flow
    - Elgot structure: looping control-flow
    - Premonoidal categories: variable binding
    - Distributivity / Strength: compatibility between variable binding and control-flow structures
  - Each _enrichment_ corresponds to a syntactic system:
    - Nothing: equivalence
    - Partial orders: refinement
    - Lattices: UB-like structure
  - We introduce a #iter-calc()-model for a function space $ms("F")$
  - We give a semantics for #iter-calc(ms("F")) in this model
  - We state:
    - _Weakening_
    - Corollary: _Coherence_
    - _Soundness of substitution_
    - _Soundness_
    - _Completeness_
  - We give a semantics for #ssa-calc(ms("E")) in this model
  - We state:
    - _Weakening_
    - Corollary: _Coherence_
    - _Soundness of substitution_
    - _Soundness_
    - _Completeness_ (later: need to work via isomorphism to #iter-calc() from (previous?) chapters)
]

#todo[
  - High-level overview diagram
  - Todo: mapping from _computational_ to _mathematical_ structures:
    - Poset-enriched categories are _sequential composition_ of computer programs.

      Two directions from here:

      - Coproducts are the same as _branching control flow_
        - If we want to add loops, we get an _iterative category_,
          but, this is not well-behaved with some advanced loop optimizations
        - To make things well-behaved, we add a _uniformity condition_ and get an _Elgot category_

      - Premonoidal are the same as _sequential composition with linear variables_
        (linear means can be used _exactly_ once)

        - A _semicartesian_ premonoidal category is  _sequential composition with affine variables_.
          We will study these later!

        -
]

#todo[
  - Categories, functors and products
  - Concrete categories and concretely cartesian categories
  - $cal(V)$-enriched categories, functors
  - $cal(V)$-enriched natural transformations; multifunctor lore
  - Introduce _monads_
  - Introduce _subcategories_, wide and full
    - $cal(V)$-enriched: injection must be a $cal(V)$-morphism
    - Introduce $ms("Rel")$: subcategories are $cset$, $ms("PFun")$, but also $ms("Rel")^+$
    - Naturally want to keep track of lattices like this
    - Previously in the paper we discuss _effect systems_
    - Can stick these on a category in the obvious manner: it's a monotone map into the subcategories
      - _Not_ necessarily join/meet-preserving! Only preserves $⊤$.
  // - Now: products; part 2. $×$ of $C_ε$ is $C_ε$ and projections are $C_⊥$
  - Coproducts and initial objects
    - Effect system interaction: $+$ of $C_ε$ is $C_ε$ and injections are $C_⊥$
  - Elgot categories
    - Uniformity w.r.t. to a subcategory
    - Uniformity w.r.t. to an effect system: needs to have $⊥$ uniform
  - Premonoidal categories
    - $⊗$ respects effects, and all $α, σ$ are $C_⊥$
    - copy-discard
    - an effect respecting copy-discard _is_ a Freyd category!
      - In particular, $cal(C)_⊥$ must be Cartesian, so we have successfully recovered the _essence_
        of a Kleisli category over a cartesian base
]

== Enriched Categories

For the rest of this thesis,
$cal(V)$ will range over concretely cartesian categories unless otherwise specified.

#definition(name: [$cal(V)$-enriched category])[
  Given a concretely cartesian category $cal(V)$,
  a $cal(V)$-enriched category $cal(C)$, or _$cal(V)$-category_, consists of
  - An set of objects $|cal(C)|$
  - For each pair of objects $A, B ∈ |cal(C)|$, a _hom-object_ $cal(C)(A, B) ∈ |cal(V)|$
  - For each object $A ∈ |cal(C)|$, an _identity morphism_ $id_A : cal(C)(A, B)$
  - For each triple of objects $A, B, C ∈ |cal(C)|$, a _composition morphism_
    $
      (;)_(A, B, C) : cal(V)(cal(C)(A, B) × cal(C)(B, C), cal(C)(A, C))
    $
]

We note that every $cal(V)$-category $cal(C)$ induces an ordinary category $U cal(C)$
with:
- The same set of objects $|U cal(C)| = |cal(C)|$
- Hom-sets $(U cal(C))(A, B) = U(cal(C)(A, B))$.

  In particular, as $U : cal(V) → cset$ is faithful, every $g ∈ (U cal(C))(A, B)$
  can be written in a unique way as an application $U f$ for $f : cal(C)(A, B)$.
- Composition given by
  $
    ∀ f : (U cal(C))(A, B), g : (U cal(C))(B, C) . f ; g = (U (;)_(A, B, C)) (f, g)
  $

In fact, this construction can be generalized quite readily:

#definition(name: "Concretely Cartesian Functor")[
  Let $F : cal(V) → cal(W)$ be a functor between concretely cartesian categories
  $(cal(V), U_cal(V))$ and $(cal(W), U_cal(W))$. We say $F$ is _concretely cartesian_ if
  - $F$ preserves erasure: $F ; U_cal(W) = U_cal(V)$
  - $F$ preserves finite products: $∀ [A_1,...,A_n] . F (Π [A_1,...,A_n]) = Π [F A_1,...,F A_n]$

  Note in particular that the erasure $U : cal(V) → cset$
  is always a concretely cartesian functor.
]

#todo[
  Neel says ok for real definition _but_ we suppress notation and pretend everything is strict;
  and also most examples are actually strict this is really just for $cal(V) × cal(W)$
]

This allows us to define the _change of basis_ of a $cal(V)$-category along a
concretely cartesian functor as follows:

#definition(name: "Change of Basis")[
  Given a concretely cartesian functor $F : cal(V) → cal(W)$ and a $cal(V)$-category $cal(C)$,
  we define its _change of basis_ $F cal(C)$ to be the $cal(W)$-category with
  - Objects $|F cal(C)| = |cal(C)|$
  - Hom objects $F cal(C)(A, B) = F(cal(C)(A, B))$
  - Identity morphisms $id_A^(F cal(C)) = id_A^(cal(C))$
  - Composition morphisms
    $
      (;)_(A, B, C)^(F cal(C)) = (F × F) ; (;)_(A, B, C)^(cal(C))
    $
]

We will often consider two particularly important cases:

- A $cset$-category $cal(C)$ is precisely an ordinary category
- A $ms("Pos")$-category $cal(C)$, i.e. a _poset-enriched category_ or _2-poset_,
  is simply a category in which
  - Each hom-set $cal(C)(A, B)$ is equipped with a partial order
  - Composition respects this partial order, i.e.,
    for all $f_1, f_2 : cal(C)(A, B)$, $g_1, g_2 ∈ cal(C)(B, C)$,
    $
      f_1 ≤ f_2 ∧ g_1 ≤ g_2 => (f_1 ; g_1) ≤ (f_2 ; g_2)
    $

Throughout the rest of this section, we fix a concretely cartesian category $cal(V)$.

#definition(name: [$cal(V)$-functor])[
  Given $cal(V)$-categories $cal(C), cal(D)$, a $cal(V)$-functor consists of
  - A mapping on objects $|F| ∈ |cal(C)| → |cal(D)|$
  - For each pair of objects $A, B ∈ |cal(C)|$, a $cal(V)$-morphism
    $
      F_(A, B) : cal(V)(cal(C)(A, B), cal(D)(F A, F B))
    $
    inducing an action on morphisms $f : cal(C)(A, B)$ by $F f = F_(A, B) f$.
]

Similarly to before,
- A $cset$-functor $cal(C)$ is precisely an ordinary functor
- A $ms("Pos")$-functor $F : cal(C) → cal(D)$... #todo[this]

#todo[just as for regular functors, we can compose $cal(V)$-functors, and there's an identity...]

#definition(name: [Category of $cal(V)$-categories])[
  The category of $cal(V)$-categories $cal(V)ms("Cat")$ has
  - Objects $|cal(V)ms("Cat")|$ $cal(V)$-categories
  - Morphisms $cal(V)ms("Cat")(cal(C), cal(D))$ $cal(V)$-functors $F : cal(C) → cal(D)$
]

#todo[
  and in particular, change-of-basis $F : cal(V) → cal(W)$
  induces $F_* : cal(V)ms("Cat") → cal(W)ms("Cat")$
]

In general, we can recover the standard category-theoretic definitions of a concept by taking $cal(V) = cset$.
Often, many definitions for $cal(V)$-categories are in fact identical;
in particular, the definitions for terminal objects, initial objects, products and coproducts are exactly the same,
so we will not repeat them.

== Premonoidal Categories

#definition(name: [$cal(V)$-Binoidal Category])[
  A $cal(V)$-binoidal category is a $cal(V)$-category equipped with
  - A function on objects $- ⊗ - ∈ |cal(C)| × |cal(C)| → |cal(C)|$
  - For each object $A ∈ |cal(C)|$, $cal(V)$-functors $A ⊗ -, - ⊗ A : cal(C) → cal(C)$ which
    agree with $- ⊗ -$ on objects

  In general, given $f: A_1 → B_1$ and $g : A_2 → B_2$, we define:
  - $f ⋉ g = f ⊗ A_2 ; B_1 ⊗ g : cal(C)(A_1 ⊗ A_2, B_1 ⊗ B_2)$
  - $f ⋊ g = A_1 ⊗ g ; f ⊗ B_2 : cal(C)(A_1 ⊗ A_2, B_1 ⊗ B_2)$

  We say that a morphism $f$ is _central_ if
  $
    ∀ A_2, B_2 ∈ |cal(C)|, ∀ g : cal(C)(A_2, B_2) . (f ⋉ g = f ⋊ g) ∧ (g ⋉ f = g ⋊ f)
  $
  In this case, we write
  $
    f ⊗ g := f ⋉ g = f ⋊ g
  $
  for the common value of $f ⋉ g$ and $f ⋊ g$.
]

#definition(name: [$cal(V)$-Premonoidal Category])[
  A $cal(V)$-premonoidal category is a $cal(V)$-binoidal category $cal(C)$
  equipped with
  - A distinguished _identity object_ $munit ∈ |cal(C)|$
  - Central natural isomorphisms:
    - $α_(A, B, C) : cal(C)((A ⊗ B) ⊗ C, A ⊗ (B ⊗ C))$ (the _associator_)
    - $λ_A : cal(C)(munit ⊗ A, A)$ (the _left unitor_)
    - $ρ_A : cal(C)(A ⊗ munit, A)$ (the _right unitor_)

  By natural, we mean that $α_(A, B, C)$. $λ_A$, and $ρ_A$ are natural in each of their components;
  i.e., for all morphisms $f: cal(C)(A, A')$, $g: cal(C)(B, B')$, and $h: cal(C)(C, C')$, the following
  _naturality squares_ hold:
  $
    (f ⊗ B) ⊗ C ; α_(A', B, C) & = α_(A, B, C) ; f ⊗ (g ⊗ h) //
                                           && : cal(C)((A ⊗ B) ⊗ C, A' ⊗ (B ⊗ C)) \
    A ⊗ (g ⊗ C) ; α_(A, B', C) & = α_(A, B, C) ; A ⊗ (g ⊗ h) //
                                           && : cal(C)((A ⊗ B) ⊗ C, A ⊗ (B' ⊗ C)) \
      A ⊗ B ⊗ h ; α_(A, B, C') & = α_(A, B, C) ; A ⊗ B ⊗ h //
                                           && : cal(C)((A ⊗ B) ⊗ C, A ⊗ (B ⊗ C')) \
            munit ⊗ f ; λ_(A') & = λ_A ; f && : cal(C)(munit ⊗ A, A') \
            f ⊗ munit ; ρ_(A') & = ρ_A ; f && : cal(C)(A ⊗ munit, A')
  $

  Such that the following coherence conditions hold:
  - (Pentagon Identity)
    For all objects $A, B, C, D ∈ |cal(C)|$, the following diagram commutes:
    $
      #diagram($
        //
        & (A ⊗ B) ⊗ (C ⊗ D) edge("dr", α_(A, B, (C ⊗ D)), ->)
        &\ ((A ⊗ B) ⊗ C) ⊗ D edge("ur", α_((A ⊗ B), C, D), ->) edge("d", α_(A, B, C) ⊗ D, ->)
        && A ⊗ (B ⊗ (C ⊗ D)) \
        (A ⊗ (B ⊗ C)) ⊗ D edge("rr", α_(A, B ⊗ C, D), ->) & & A ⊗ ((B ⊗ C) ⊗ D)
        edge("u", A ⊗ α_(B, C, D), ->)
      $)
    $

  - (Triangle Identity)
    For all objects $A, B ∈ |cal(C)|$, the following diagram commutes:
    $
      #diagram(cell-size: 15mm, $
        //
        (A ⊗ munit) ⊗ B edge(α_(A, munit, B), ->) edge("dr", ρ_A ⊗ id_B, ->, label-side: #right)
        & A ⊗ (munit ⊗ B) edge("d", id_A ⊗ λ_B, ->, label-side: #left) \
        & A ⊗ B
      $)
    $

    We say that a $cal(V)$-premonoidal category is _symmetric_ if it is equipped with an additional
    central natural isomorphism
    - $σ_(A, B) : cal(C)(A ⊗ B, B ⊗ A)$ (the _braiding_)

    Satisfying:
    - (Naturality): $∀ f : cal(C)(A, A') . f ⊗ B ; σ_(A', B) = σ_(A, B) ; B ⊗ f
      : cal(C)(A ⊗ B, B ⊗ A')$
    - (Symmetry): $σ_(A, B)^(-1) = σ_(B, A)$

    Such that the following coherence conditions hold:
    - (Hexagon Identity)
      For all objects $A, B, C ∈ |cal(C)|$, the following diagram commutes:
      $
        #diagram($ (A ⊗ B) ⊗ C edge(α_(A, B, C), ->) edge("d", σ_(A, B) ⊗ C, ->, label-side: #right) &
        A ⊗ (B ⊗ C) edge(σ_(A, B ⊗ C), ->, label-side: #left) &
        (B ⊗ C) ⊗ A edge("d", α_(B, C, A), ->, label-side: #left) \
        (B ⊗ A) ⊗ C edge(α_(B, A, C), ->, label-side: #right) &
        B ⊗ (A ⊗ C) edge(B ⊗ σ_(A, C), ->, label-side: #right) &
        B ⊗ (C ⊗ A) $)
      $
]

#definition(name: [Freyd Category])[
  #todo[this]
]

#definition(name: [$n$-ary Tensor Product])[
  Given a $cal(V)$-premonoidal category $cal(C)$...
  #todo[finish definition]
]

#todo[
  - In the literature, we have:
    - A Freyd category is a _choice_ of $cal(C)_⊥$
      - $cal(C)_⊥$ is structure for Freyd
      - Is property in the copy-discard / Markov worlds
    - _copy-discard_ categories, which are premonoidal + comonoids
      - These _induce_ a Freyd category
      - A morphism is _relevant_ if ...
      - A morphism is _affine_ if ...
      - What if I want to keep track of which morphisms are relevant/affine/central?
      - I need more structure
    - Effectful category
      - An effect system $cal(E)$ is just a bounded lattice with monotone functions
        is relevant, is affine, is central
      - An effectful category over an effect system $cal(E)$ maps effects to subcategories with
        $⊤$ to top
      - Morphisms between effect systems induce identity-on-objects functors
        between effectful categories
      - A Freyd category is just an effectful category over ${⊤, ⊥}$
      - A Cartesian category is just an effectful category over ${⊥}$
]

== Semantics of Expressions

#include "content/semantics-of-ssa/semantics-of-expressions.typ"

== Equational Models

#todo[Category of $cal(V)$-enriched SSA models]

#todo[Syntactic $cal(V)$-enriched SSA model]

#todo[Modeling an equational theory $req$ w.r.t. an effect system $cal(E)$]

#todo[Full subcategory]

#todo[Soundness of Equivalence]

#todo[Completeness of Equivalence]

#todo[Initiality]

== Refinement Models

#todo[Modeling a refinement theory $ms("R")$ w.r.t. a _linear_ effect system $cal(E)$]

#todo[Soundness of Refinement]

#todo[Completeness of Refinement]

== Semantics of Regions

#include "content/semantics-of-ssa/semantics-of-regions.typ"

= Monadic Models of SSA <concrete-models>

== Monad Transformers, Partiality, Nondeterminism, Logging, and State

#todo[Partiality over #cset]

== $cal(V)$-Enriched Monads and Monad Transformers

#todo[_All_ of the above are $cal(V)$-enriched!]

#the-bibliography

#pagebreak()

#let appendix(body) = {
  set heading(numbering: "A", supplement: [Appendix])
  counter(heading).update(0)
  (thesis-state.update)(appendix-state)
  [ #body <appendix> ]
}

#show: appendix

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
