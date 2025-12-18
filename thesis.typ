#import "@preview/simplebnf:0.1.1": *
#import "@preview/subpar:0.2.2"
#import "@preview/lemmify:0.1.8": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node


#let (
  theorem,
  lemma,
  corollary,
  remark,
  proposition,
  example,
  proof,
  rules: thm-rules,
) = default-theorems("thm-group", lang: "en")

#let (
  definition,
  rules: thm-rules-b,
) = default-theorems("thm-group-b")

#show: thm-rules

#show: thm-rules-b

#import "@preview/wordometer:0.1.5": word-count
#show: word-count.with(exclude: (<no-wc>, <appendix>))

#let production = false;

#import "thesis-template.typ": *
#import "todos.typ": *

#import "syntax.typ": *

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

= Static Single Assignment (SSA)

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
          Or[$(V) = o seq β$][_destructure_]
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
      := (fexpr(fnum(0), x_0),..., fexpr(fnum(n - 1), x_(n - 1)))
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
        }),
        Prod($v$, {
          Or[$x$][_variable_]
          Or[$(V)$][_struct_]
        }),
        Prod($V$, {
          Or[$·$][]
          Or[$V, fexpr(lb("f"), x)$][]
        }),
      ),
      bnf(
        Prod($β$, {
          Or[$x = o seq β$][_assign_]
          Or[$(V) = o seq β$][_destructure_]
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
        Prod($v$, {
          Or[$x$][_variable_]
          Or[$(V)$][_struct_]
        }),
        Prod($V$, {
          Or[$·$][]
          Or[$V, fexpr(lb("f"), x)$][]
        }),
      ),
      bnf(
        Prod($o$, {
          Or[$v$][_value_]
          Or[$f med v$][_application_]
        }),
        Prod($f$, {
          Or[$p$][_app_]
          Or[$lb("l", annot: lb("L"))$][_label_]
        }),
      ),
      bnf(Prod($r$, {
        Or[$x = o seq r$][_assign_]
        Or[$(V) = o seq r$][_destructure_]
        Or[$τ seq L$][_terminator_]
      })),

      bnf(
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
            Or[$(E)$][_tuple_]
            Or[$elet(x, e_1, e_2)$][_let-binding_]
            Or[$elet((V), e_1, e_2)$][_destructure_]
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
      bnf(Prod($r$, {
        Or[$x = e seq r$][_assign_]
        Or[$(V) = e seq r$][_destructure_]
        Or[$τ seq L$][_terminator_]
      })),

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
      bnf(
        Prod($L$, {
          Or[$·$][]
          Or[$L seq gbr(lb("l"), x, {r})$][]
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
        Or[$(V) = e seq r$][_destructure_]
        Or[$brb(lb("l"), e)$][_branch_]
        Or[$scase(e, L)$][_case_]
        Or[${ r } seq L$][_terminator_]
      })),
      bnf(
        Prod($L$, {
          Or[$·$][]
          Or[$gbr(lb("l"), x, {r}) seq L$][]
        }),
        Prod($lb("L")$, {
          Or[$·$][]
          Or[$lb("L"), lb("l")(A)$][]
        }),
      ),
    )
  ],
  caption: [
    Grammar for type-theoretic SSA with expressions (#gssa-calc(iter-calc()))
  ],
  kind: image,
) <tt-ssa-grammar>

= Conventions and Notation

#todo[add introduction to section; push some definitions and extra background to appendix?]

#todo[Collapse subsections, reformat]

== Foundations

We work in (informal) Grothendieck-Tarski set theory. In particular,
- We assume _Tarski's axiom_: every set is an element of some Grothendieck universe $cal(U)$.
- In particular, we postulate an infinite hierarchy of Grothendieck universes $cal(U)_ℓ$
- We call an element of $cal(U)_ℓ$ _ℓ-small_
- Definitions are implicitly $ℓ$-polymorphic unless stated otherwise.
  For example, when we define a category, we really mean an $ℓ$-category with $ℓ$-small hom-sets.

== Finite sets

We define the canonical _finite set with $n$ elements_ $fin(n)$
to consist of the first $n$ natural numbers:
$
  fin(n) := { i ∈ ℕ | i < n }
$
Note that, following the convention in computer science, we start counting from $0 ∈ ℕ$.

/*
We fix a canonical isomorphism
$
  fcanon(m, n) := (λ i . site(i < m, i, i - m))
  : fin((m + n)) ≅ fin(m) + fin(n)
$
*/

== Families

An _($I$-indexed) family_ @nlab:family $icol(a) := (a_i | i ∈ I)$ consists of

- An _index set_ $I$, whose elements are the _indices_ of the family.
  We will sometimes write $cix(icol(a)) := I$.

- For each index $i ∈ I$, an _element_ $a_i$.
  We will sometimes write this as a function application $icol(a) med i$.

We will often write an indexed family as $(i ↦ a_i)_(i ∈ I)$ or $(a_i)_(i ∈ I)$,
or even $(i_1 ↦ a_(i_1),...,i_n ↦ a_(i_n))$ for $I = {i_1,...,i_n}$ finite.
In general, we will omit $I$ when clear from context.

We write the empty indexed family as $()$.

We say $icol(a)$ is a _subfamily_ of $icol(b)$, written $icol(a) ⊆ icol(b)$, if
$cix(icol(a)) ⊆ cix(icol(b))$
and
$∀ i ∈ cix(icol(a)), a_i = b_i$.

/*
Type-theoretically, an indexed collection $(i ↦ a_i)_(i ∈ I)$ is just a dependent function type
$Π i : I . A_i$; set-theoretically, we can model it as a set of pairs ${(i, a_i) | i ∈ I}$
forming the graph of a well-defined function.
*/

Given families $icol(a) = (a_i | i ∈ I)$, $icol(b) = (b_j | j ∈ J)$,
we define the _reindexings_ of $icol(a)$ _along_ $icol(b)$ as follows:
$
  hfam(icol(a), icol(b)) := { f : J → I | ∀ j ∈ J . a_(f(j)) = b_j }
$

We note that

- We always have $id_I : hfam(icol(a), icol(a))$

- If $f : hfam(icol(a), icol(b))$ and $g : hfam(icol(b), icol(c))$,
  then $f ∘ g : hfam(icol(a), icol(c))$ (_not_ $g ∘ f$!)

  For clarity, we will write this as $f famcomp g$ to emphasize that $f$ is a reindexing.

An injective reindexing is called a _thinning_,
while a bijective reindexing is called a _permutation_.
We denote the sets of such reindexings as
$
  hthin(icol(a), icol(b)) & := { f ∈ hfam(icol(a), icol(b)) | f "is injective" } \
  hperm(icol(a), icol(b)) & := { f ∈ hthin(icol(a), icol(b)) | f "is bijective" } \
$

Both these subsets contain the identity reindexing and are closed under (reverse) composition.
Furthermore, the set of permutations is closed under inverses (which always exist):
$
  ∀ f ∈ hperm(icol(a), icol(b)), f^(-1) ∈ hperm(icol(b), icol(a))
$

/*
TODO: separate _ordered_ collection section... or just list...

If $I$ and $J$ are equipped with a preorder, we say a reindexing $f : hfam(icol(a), icol(b))$ is
- _order-preserving_ or _monotone_ if $∀ j sle(J) j' . f(j) sle(I) f(j')$
- _order-reflecting_ if $∀ j, j' . f(j) sle(I) f(j') ⇒ j sle(J) j'$
- _order-embedding_ if it is both monotone and reflecting,
  i.e. if $∀ j, j' . j sle(J) j' <==> f(j) sle(I) f(j')$
*/

We define some of the basic operations on indexed families as follows:

- Given indexed families $icol(a) = (a_i | i ∈ I)$, $icol(b) = (b_i | j ∈ J)$,
  we define their _override_ as follows:
  $
    icol(a) ovrd icol(b) = [λ k . site(k ∈ I, a_k, b_k) | k ∈ I ∪ J]
  $

  We note that
  - $lnil ovrd icol(a) = icol(a) ovrd lnil = icol(a)$
  - $icol(a) ovrd (icol(b) ovrd icol(c)) = (icol(a) ovrd icol(b)) ovrd icol(c)$
  - $icol(a) ovrd icol(b) = icol(b) ovrd icol(a) <==> ∀ i ∈ I ∩ J . a_i = b_i$
    in which case we write $icol(a) ∪ icol(b)$.

    If $icol(a)$ and $icol(b)$ are in fact disjoint, we write $icol(a) ⊔ icol(b)$.


- We define the _selection_ of $J ⊆ I$ from an indexed family $icol(a) = (a_i | i ∈ I)$
  as follows:
  $
    csel(icol(a), J) = (a_i | i ∈ I ∩ J)
  $

- We define the _removal_ of $J ⊆ I$ from an indexed family $icol(a) = (a_i | i ∈ I)$
  as follows:
  $
    crem(icol(a), J) = (a_i | i ∈ I sdiff J)
  $

  We note that
  $icol(a)[J] ⊔ (icol(a) sdiff J) = (icol(a) sdiff J) ⊔ icol(a)[J] = icol(a)$.

/*
- Given a function $f$, we define the pointwise map of a family $icol(a)$ to be given by
  $
    f cmap [a_i | i ∈ I] = [f med a_i | i ∈ I]
  $

  This satisfies the usual properties of a functor:

  - $id cmap icol(a) = icol(a)$
  - $(g ∘ f) cmap icol(a) = g cmap (f cmap icol(a))$

- Likewise, we define the _application_ of two families $icol(f), icol(a)$ as follows:
  $
    [f_i | i ∈ I] capp [a_j | j ∈ J] = [f_i med a_i | i ∈ I ∩ J]
  $

- And the _zip_ of two families $icol(a), icol(b)$ as follows:
  $
    [a_i | i ∈ I] czip [b_j | j ∈ J] = [(a_i, b_i) | i ∈ I ∩ J]
  $
*/

- We may define the _coproduct_ of two indexed families
  $icol(a) = (a_i | i ∈ I)$,
  $icol(b) = (b_j | j ∈ J)$ using the pointwise map as follows:
  $
    icol(a) + icol(b)
    = (linj i ↦ a_i | i ∈ I) ⊔ (rinj j ↦ b_j | j ∈ J)
  $

  This has projection thinnings
  $
    lthin(icol(a), icol(b)) := (λ i . linj i) : hthin(icol(a) + icol(b), icol(a)) quad quad
    rthin(icol(a), icol(b)) := (λ j . rinj j) : hthin(icol(a) + icol(b), icol(b))
  $

- Likewise, we may define the _product_ of two indexed families
  $icol(a) = (a_i | i ∈ I)$,
  $icol(b) = (b_j | j ∈ J)$ as follows:
  $
    icol(a) × icol(b) = ((i, j) ↦ (a, b) | (i, j) ∈ I × J)
  $

== Lists, Streams, and Sequences

- A _sequence_ $icol(a) = [a_i | i ∈ I]$ is an indexed family $(a_i | i ∈ I)$ where
  - $I = ℕ$ , in which case we call $icol(a)$ a _stream_, or
  - $I = fin(n)$ for some $n ∈ ℕ$, in which case we call $icol(a)$ a _list_ or _$n$-tuple_.

  In general, we will reserve square brackets $[ - ]$ for lists
  (rather than general indexed families), writing

  - $lnil := ()$ for the empty list
  - $[a_0,...,a_(n - 1)]$ for a list of length $n$
  - $[a_0, a_1, a_2, ...]$ for a stream
  - _Comprehensions_ $[f(a) | a ∈ icol(a)] := [f(a_i) | i ∈ I]$

    In general, we will often interpret $ℕ$ and $fin(n)$ as a stream and a list.

  Note that, following the convention in computer science, our sequences are _zero-indexed_.

- Given an arbitrary sequence $icol(a)$, we can append an element $x$ to the front of $icol(a)$
  to form a new sequence $x :: icol(a)$ (pronounced "$x$ _cons_ $icol(a)$") as follows:
  $
    x :: icol(a)
    := [λ | 0 => x | i + 1 => icol(a) med i]
    = [x, a_0, a_1, ...]
  $

  If $icol(a)$ is in fact finite, we may append an element $x$ to the back,
  forming a new sequence $icol(a) lsnoc x$ (pronounced "$icol(a)$ _snoc_ $x$") analogously:
  $
    icol(a) lsnoc x
    := [λ i . site(i < |icol(a)|, icol(a) med i, x)]
    = [a_0, a_1, ..., a_(n - 1), x]
  $

- We define the _concatenation_ of a list $icol(a)$ to a sequence $icol(b)$,
  written $icol(a) lcat icol(b)$, by induction on $icol(a)$ as follows:
  $
    lnil lcat icol(b) = icol(b) quad quad quad
    (x :: icol(a)) lcat icol(b) = x :: (icol(a) lcat icol(b))
  $

  For $icol(a)$ of length $n$, we can show by induction that
  $
    icol(a) lcat icol(b)
    = [a_0,...,a_(n - 1),b_0, b_1, ...]
    = [λ i . site(i < n, a_i, b_(i - n))]
  $

  In particular, we note that
  $
    lnil lcat icol(a) = icol(a) lcat lnil = icol(a) quad quad quad
    [a] lcat icol(a) = a :: icol(a) quad quad quad
    icol(a) lcat [b] = icol(a) lsnoc b
  $
  $
    icol(a) lcat (icol(b) lcat icol(c)) = (icol(a) lcat icol(b)) lcat icol(c)
  $

- We define the _repetition_ of a list $icol(a)$, written $n · icol(a)$, by induction as follows:
  $
    0 · icol(a) = lnil quad quad quad (n + 1) · icol(a) = icol(a) lcat n · icol(a)
  $

= Type Theory

== Typing Rules

=== Types and Contexts

#todo[introduce types]

#figure(
  [
    #bnf(
      Prod($A$, {
        Or[$tybase(X)$][_base type_ $X ∈ ms("X")$]
        Or[$Σ lb("L")$][_Σ (coproduct)_]
        Or[$Π lb("T")$][_Π (product)_]
      }),
      Prod($lb("L")$, {
        Or[$·$][]
        Or[$lb("L"), lty(lb("l"), A)$][]
      }),
      Prod($lb("T")$, {
        Or[$·$][]
        Or[$lb("T"), fty(lb("f"), A)$][]
      }),
    )
    $
      A × B & := Π ( lb("l") : A, lb("r") : B ) & #h(3em) & mb(1) & := Π · \
      A + B & := Σ ( lb("l")(A), lb("r")(B) )   &         & mb(0) & := Σ ·
    $
    $
      Π [A_0,...,A_(n - 1)] & = Π_i A_i & := Π ( lb("p")_0 : A_0, ..., lb("p")_(n - 1) : A_(n - 1) ) \
      Σ [A_0,...,A_(n - 1)] & = Σ_i A_i &   := Σ ( lb("i")_0(A_0), ..., lb("i")_(n - 1)(A_(n - 1)) )
    $
    \
  ],
  caption: [Grammar for simple types parametrized by base types $ms("X")$]
)

#todo[
  We treat $lb("L"), lb("T")$ as _label-indexed families_, quotiented by order

  For example, we could sort by labels, and assume no duplicates.

  Note on the locally-nameless trick
]

#todo[introduce _weakening_ of types]

#let r-twk-base = rule(
  name: "base",
  $X, Y ∈ ms("X")$,
  $X sle(X) Y$,
  $atywk(X, Y, ms("X"))$,
);

#let r-twk-sigma = rule(
  name: $Σ$,
  $atywk(Σ lb("T"), Σ lb("T"'), ms("X"))$,
  $atywk(A, A', ms("X"))$,
  $atywk(Σ (lb("T"), lty(lb("f"), A)), Σ (lb("T")', lty(lb("f"), A')), ms("X"))$,
);

#let r-twk-pi = rule(
  name: $Π$,
  $atywk(Π lb("T"), Π lb("T"'), ms("X"))$,
  $atywk(A, A', ms("X"))$,
  $atywk(Π (lb("T"), fty(lb("f"), A)), Π (lb("T")', fty(lb("f"), A')), ms("X"))$,
);

#let r-twk-unit = rule(
  name: $tunit$,
  $atywk(A, Π [], ms("X"))$,
);

#let r-twk-zero = rule(
  name: $tzero$,
  $atywk(A, Σ [], ms("X"))$,
);

#figure(
  [
    #rule-set(
      declare-rule(r-twk-base, label: <twk-base>),
      declare-rule(r-twk-sigma, label: <twk-sigma>),
      declare-rule(r-twk-pi, label: <twk-pi>),
      declare-rule(r-twk-unit, label: <twk-unit>),
      declare-rule(r-twk-zero, label: <twk-zero>),
    )
    \ 
  ],
  caption: [Weakening for simple types $sty(ms("X"))$],
)

#lemma[
  If $sle(ms("X"))$ is a partial order, so is $tyle(ms("X"))$
]

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

#todo[not quite the same as distinguishing $lb("T"), lb("L")$, since _these_ have different variance]

=== Expressions

#todo[introduce concept of a function space]

#todo[fix notation for function space judgement]

#todo[IMPORTANT: while $Π$-types are unordered, tuples $(E)$ are _ordered_ left-to-right!]

#figure(
  [
    #rule-set(
      declare-rule(rule(
        name: "var",
        $Γ med x = A$,
        $hasty(Γ, x, A)$,
      )),
      declare-rule(rule(
        name: "app",
        $isfn(Γ, f, A, B)$,
        $hasty(Γ, a, A)$,
        $hasty(Γ, f med a, B)$,
      )),
      declare-rule(rule(
        name: "inj",
        $hasty(Γ, a, A)$,
        $hasty(Γ, lb("l") med a, Σ lty(lb("l"), A))$,
      )),
      declare-rule(rule(
        name: "tuple",
        $istup(Γ, E, lb("T"))$,
        $hasty(Γ, (E), Π lb("T"))$,
      )),
      declare-rule(rule(
        name: "Π-nil",
        $istup(Γ, ·, ·)$,
      )),
      declare-rule(rule(
        name: "Π-cons",
        $istup(Γ, E, lb("T"))$,
        $hasty(Γ, e, A)$,
        $istup(Γ, #$E, e$, #$lb("T"), fty(lb("f"), A)$)$
      )),
      declare-rule(rule(
        name: "cases",
        $hasty(Γ, e, Σ lb("L"))$,
        $isebrs(Γ, lb("L"), M, A)$,
        $hasty(Γ, ecase(e, M), A)$
      )),
      declare-rule(rule(
        name: "Σ-nil",
        $isebrs(Γ, ·, ·, ·)$,
      )),
      declare-rule(rule(
        name: "Σ-cons",
        $isebrs(Γ, lb("L"), M, A)$,
        $hasty(#$Γ, x : A$, a, A)$,
        $isebrs(Γ, #$lb("L"), lty(lb("l"), A)$, #$M, ebr(lb("l"), x, a)$, A)$,
      )),
    )
  ],
  caption: [Typing rules for #iter-calc($F$)],
)

=== Regions

#todo[introduce concept of an expression space]

#todo[fix notation for expression space judgement]

#figure(
  [
    #todo[this]
  ],
  caption: [Typing rules for #ssa-calc($E$)],
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

#figure(
  [
    #todo[this]
  ],
  caption: [Equivalence rules for #iter-calc($F$)],
)

#figure(
  [
    #todo[this]
  ],
  caption: [Congruence rules for #iter-calc() equivalence],
)

=== Effects

#figure(
  [
    #todo[this]
  ],
  caption: [Effect rules for #iter-calc()],
)

=== Refinement

#figure(
  [
    #todo[this]
  ],
  caption: [Refinement rules for #iter-calc()],
)

=== Linearity

#figure(
  [
    #todo[this]
  ],
  caption: [Linearity rules for #iter-calc()],
)

== Regions

=== Effects

#figure(
  [
    #todo[this]
  ],
  caption: [Effect rules for #iter-calc()],
)

=== Refinement

#figure(
  [
    #todo[this]
  ],
  caption: [Refinement rules for #ssa-calc()],
)

=== Linearity

#figure(
  [
    #todo[this]
  ],
  caption: [Linearity rules for #ssa-calc()],
)

= Normalization

== Compiling #gssa-calc(iter-calc()) to #iter-calc()

== Compiling #iter-calc() to #ssa-calc()

== Normalizing #gssa-calc(iter-calc()) to #gssa-calc()

== Normalizing #gssa-calc() to #ssa-calc()

/*

== From RTL to SSA

#todo[what is RTL, and why is it a cool IR, in more detail]

One of the earliest compiler IRs introduced is _register transfer language_ (_RTL_) @allen-70-cfa,
commonly referred to as _three-address code_.
An RTL program consists of a _control-flow graph_ (CFG) $G$
with a distinguished, nameless entry block.
Each node of the CFG corresponds to a _basic block_ $β$,
which is a straight-line sequence of _assignments_ $x = f(y, z)$
#footnote[
  Hence the name "3-address code," referring to the three variables $x, y, z$.
  Assignments $x = y + z$ are often referred to as _quads_ @aho-11-dragon,
  since they have four arguments:
  three variables, and the operator $+$.
]
followed by a _terminator_ $τ$,
which tells us where to transfer control next.

In @rtl-grammar, we give a formal presentation of the syntax of RTL parametrized by a set of
_primitive instructions_ $p ∈ cal(I)$.
Our grammar is intentionally minimal, with many important features implemented via syntax sugar:
- _Constants_ $c$ are represented as nullary primitive instructions $c()$.
- _Operations_ $o$ always return a single value of fixed type; in particular,
- Operations can produce multiple values by returning a tuple; which can be de-structured by
  assigning it to a tuple of variables $(V)$ #footnote[
    Note the unusual fact that this means the production $(V)$ for a variable list may appear on
    both the left-hand side and right-hand side of an assignment.
  ]
- _Conditional branches_ $ite(x, τ, τ')$ are desugared to
  _switch-statements_
  $
    sswitch(o, lb("tt"): τ seq lb("ff"): τ')
  $
  where $lb("tt"), lb("ff") ∈ tbool$ are distinguished labels.
  In general, for every finite set of labels $lb("l") ∈ lb("L")$,
  we postulate an _enumeration type_ with members of the form $lb("l", annot: lb("L"))$;
  where $lb("L")$ is clear from context, we omit it.

#figure(
  placement: auto,
  [
    #grid(
      align: left,
      columns: 3,
      gutter: (2em, 0em),
      bnf(
        Prod($v$, {
          Or[$x$][_variable_]
          Or[$(V)$][_tuple_]
        }),
        Prod($V$, {
          Or[$·$][]
          Or[$x, V$][]
        }),
      ),
      bnf(
        Prod($o$, {
          Or[$v$][_value_]
          Or[$f med v$][_application_]
        }),
        Prod($f$, {
          Or[$p$][_app_]
          Or[$lb("l", annot: lb("L"))$][_label_]
        }),
      ),
      bnf(Prod($β$, {
        Or[$x = o seq β$][_assign_]
        Or[$(V) = o seq β$][_destructure_]
        Or[$τ$][_terminator_]
      })),

      bnf(
        Prod($τ$, {
          Or[$brb(lb("l"))$][_branch_]
          Or[$sswitch(o, B)$][_case_]
        }),
        Prod($B$, {
          Or[$·$][]
          Or[$ssbr(lb("l₁"), brb(lb("l₂"))), B$][]
        }),
      ),
      bnf(Prod($G$, {
        Or[$β$][_entry_]
        Or[$G seq lb("l") : β$][]
      })),
      bnf(Prod($lb("L")$, {
        Or[$·$][]
        Or[$lb("l"), lb("L")$][]
      })),
    ),
  ],
  caption: [
    Grammar for RTL.

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
                  \
                  \
                  \
                  \
                  \
                  \
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
      lb("loop"): & i₁ = #eϕ($lb("entry") : i₀, lb("body") : i₂$) \
                  & a₁ = #eϕ($lb("entry") : a₀, lb("body") : a₂$) \
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
  caption: todo-inline[BBA grammar],
) <bba-grammar>

#figure(
  todo[this],
  caption: todo-inline[BBA factorial],
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

#block-note[
  Weird syntax idea, we discussed this and you rejected it for TOPLAS but makes sense for thesis:
  no where-blocks, just curly braces.

  Neel says: go do it
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
This, especially combined with change (3),
makes it much easier to verify optimizations such as
#todo[clean up optimization here; also no more where]
/*
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
*/
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

#todo[
  At a high level:
  - $lb("L")$ is a list of labels and types; here $lb("l")$ is sugar for $lb("l")(mb(1))$
]

#block-note[
  - We introduce λiter at the end of section 2 as our expression language
  - We want to mention that our expression language has the same power as SSA and give a pointer to
    the proof down at the end (post-completeness)
  - Minimize forward references considered harmful
]

#figure(
  placement: auto,
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
            Or[$f med e$][_application_]
            Or[$(E)$][_tuple_]
            Or[$elet(x, e_1, e_2)$][_let-binding_]
            Or[$elet((V), e_1, e_2)$][_destructure_]
            Or[$ecase(e, C)$][_cases_]
            Or[$eiter(e_1, x, e_2)$][_iteration_]
          },
        ),
      ),
      bnf(
        Prod(
          $E$,
          {
            Or[$·$][_nil_]
            Or[$e, E$][_cons_]
          },
        ),
        Prod(
          $C$,
          {
            Or[$·$][_nil_]
            Or[$ebr(lb("l"), x, a) seq C$][_cons_]
          },
        ),
      )
    )
  ],
  caption: [
    Grammar for #iter-calc
  ],
  kind: image,
) <iter-calc-grammar>

#todo[
  Question for Neel:
  - Start with SSA _or_ Start with #iter-calc
    - #iter-calc makes some sense...
]

#todo[fuse with refined account of SSA]

== Effect Systems

<effect-system>

/*

We now give a formal account of #ssa-calc, starting with the types.
Our types are first order,
and consists of binary sums $A + B$, products $A times.o B$, the $tunit$ type $mb(1)$,
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
- An empty tuple $()$, which types in any context by #todo-inline[rle:$tunit$]
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
If-then-else is then a $ms("case")$ which ignores the $tunit$ payloads,
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
- #todo[while you're rewriting this, no more where]
  /*
  _$ms("where")$-blocks_ of the form "$where(r, (wbranch(ℓ_i, x_i, t_i))_i)$",
  which consist of a family of mutually recursive regions $wbranch(ℓ_i, x_i, t_i)$
  and a _terminator region_ $r$ which may branch to one of $ℓ_i$ or an exit label.
  */

*/

#todo[figure: rules for typing isotopessa regions]

== Metatheory

/*

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
- #todo-inline[terminal], which equates all _pure_ terms of $tunit$ type $mb(1)$. Note that
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

#todo[no more where]
/*
To state our $eta$-rule, however, we will need to introduce some more machinery. Given a mapping
from a set of labels $ℓ_i$ to associated regions $t_i$, we may define the _control-flow
graph substitution_ $cfgsubst((wbranch(ℓ_i, x_i, t_i),)_i)$ pointwise as follows:
$
  cfgsubst((wbranch(ℓ_i, x_i, t_i),)_i) space kappa space a
  := (where(brb(kappa, a), (wbranch(ℓ_i, x_i, t_i),)_i))
$
*/
In general, we may derive, for any label-context $ms("L")$ (assuming $cfgsubst(dot)$ acts uniformly
on the labels $kappa$ in $ms("L")$ as described above), the following rule #todo-inline[cfgs].

#todo[no more where]
/*
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
*/
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
#todo[no more where]
/*
$
  lbeq(
    #$Gamma, bhyp(x, A)$, [e slash y]s, where(t, wbranch(ℓ, x, brb(kappa, e))),
    #$ms("L"), kappa(B)$
  )
$
*/
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
#todo[also no more where]
/*
$
  lbeq(
    Gamma, where(
      (where(r, wbranch(ℓ, x, brb(kappa, e)))),
      wbranch(kappa, y, s)
    ), where(r, t), ms("L")
  )
$
*/
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
#todo[yet less where]
/*
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
*/
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

#todo[also no more where]
/*
It's easy to see that $(where(([ℓ(x) arrow.bar brb(kappa, e)]r), wbranch(kappa, y, s)))$ and
$(where(r, t))$ are syntactically equal to the _RHS_ and _LHS_ of our desired result
*/
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
*/

*/

= Category Theory

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

#todo[one more quick pass]

// At a high level, our goal is to assign a denotational semantics $⟦hasty(Γ, a, A)⟧$
// to every well-typed #iter-calc program $hasty(Γ, a, A)$.

We will begin with a brief overview of basic category theory, in which we will take the opportunity
to fix notations. Recall the definition of a category $cal(C)$:

#definition(name: "Category")[
  A category $cal(C)$ is given by:
  - A set of _objects_ $|cal(C)| ∈ cal(U)_ℓ$
    #footnote[
      A category with objects in $cal(U)_ℓ$ is called _$ℓ$-small_.
      For the rest of this paper, we will work polymorphically in $ℓ$,
      and hence leave it unspecified.
    ]
  - For each pair of objects $A, B in |cal(C)|$, a set of _morphisms_ $cal(C)(A, B)$.
    We call this set a _hom-set_.
  - For each object $A in |cal(C)|$, an _identity morphism_ $id_A : cal(C)(A, A)$
  - A binary operation, $- med ; -$, mapping each pair of morphisms $f : cal(C)(A, B)$ and $g : cal(C)(B, C)$
    to their _composition_ $f ; g : cal(C)(A, C)$

  Such that:
  - For all $A, B: |cal(C)|$, $id_A ; f = f ; id_B = f$
  - For all $f: cal(C)(A, B), g: cal(C)(B, C), h: cal(C)(C, D)$, $(f ; g) ; h = f ; (g ; h)$

  We will sometimes write the set $cal(C)(A, B)$ as $A ahm(cal(C)) B$ or,
  where $cal(C)$ is clear from context, $A -> B$.
]

We follow the convention in computer science and define composition "forwards" as $f ; g$.
If we interpret objects $A, B$ as _states_
and morphisms $f: cal(C)(A, B), g : cal(C)(B, C)$ as _transformations between states_,
then their _sequential composition_
$
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B edge(g, ->) & C $)
$
is precisely $f ; g : cal(C)(A, C)$: the composite path from $A$ to $C$ through $B$.

#todo[nicer introduction to commutative diagrams]

#todo[general principle: as fast as possible, change algebra to geometry!]

Viewing morphisms in a category as diagrams, the laws of a category become graphically obvious:
if the identity transformation from $A$ to $A$ is doing nothing, i.e. the null path, then the
axiom that
$
  id_A ; f = f ; id_B = f
$
becomes the (trivial) equation on diagrams
$
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B $)
  quad = quad
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B $)
  quad = quad
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B $)
$
Likewise, the associativity axiom becomes the (trivial) equation
$
  #diagram(cell-size: 15mm, $ A edge(f, ->) & B edge(g, ->) & C edge(h, ->) & D $)
$

#definition(name: "Category of sets")[
  We define the category of sets to have
  objects sets $A$
  and morphisms $f : cset(A, B)$ functions $f : A → B$.

  Composition $f ; g$ is simply (pointwise) composition of functions $g ∘ f$.
]

#todo[category of posets]

#todo[category of reindexings]

#todo[_subcategory_ of thinnings, permutations]

#definition(name: "Isomorphism, Epimorphism, Monomorphism")[
  Given a morphism $f : cal(C)(A, B)$,

  - $f$ is an _isomorphism_ if there exists an _inverse morphism_ $g : cal(C)(B, A)$
    such that $f ; g = id_A$ and $g ; f = id_B$.
    //
    If such a morphism exists, it is unique, so we may write it as $f^(-1)$.

    Two objects $A, B : |cal(C)|$ are _isomorphic_, written $A ≈ B$, if there exists
    an isomorphism $f : cal(C)(A, B)$.

  - $f$ is an _epimorphism_ if, for all parallel morphisms $g_1, g_2 : cal(C)(B, X)$,
    $f ; g_1 = f ; g_2$ implies $g_1 = g_2$.
    //
    In this case, we will say $f$ is _epic_.

  - $f$ is a _monomorphism_ if, for all parallel morphisms $h_1, h_2 : cal(C)(X, A)$,
    $h_1 ; f = h_2 ; f$ implies $h_1 = h_2$.
    //
    In this case, we will say $f$ is _monic_.
]

#todo[identification of isomorphic objects]

In $cset$, a function $f: A → B$ is
- an epimorphism iff it is _surjective_;
- a monomorphism iff it is _injective_;
- an isomorphism iff it is a _bijection_.

While in $cset$, any morphism which is both surjective and injective is in fact a bijection,
it is _not_ generally the case that a morphism which is both epic and monic is an isomorphism!

#todo[epis, monos, and isos are always subcategories]

#definition(name: "Functor")[
  Given categories $cal(C), cal(D)$, a _functor_ $F : cal(C) → cal(D)$ consists of:
  - A mapping on objects $|F| : |cal(C)| → |cal(D)|$. We often simply write $|F|(A)$ as $F A$.
  - A mapping from $cal(C)$-morphisms $f : cal(C)(A, B)$
    to $cal(D)$-morphisms $F f : cal(D)(F A, F B)$
  such that
  - $F$ preserves identities: $F id_A = id_(F A)$
  - $F$ preserves composition: $F (f ; g) = (F f) ; (F g)$
]

#todo[_forgetful functor_ from $cposet$ to $cset$]

#todo[_forgetful functor_ from $cfam$ to $cset$]

#todo[_forgetful functor_ from $cperm$ to $cthin$ to $cfam$]

#todo[define a full functor]

In general,
- We say a functor $F$ is _faithful_ if its action on morphisms is _injective_; i.e.,
  $
    ∀ f, g : cal(C)(A, B) . F f = F g <==> f = g
  $

#todo[full and faithful iff bijection on hom-sets]

- A functor $F : cal(V) → cal(V)$ is _identity on objects_ if $|F| = id_(|cal(V)|)$.

#todo[the first one is _full_, but _not_ faithful]

#todo[the other two are]

#todo[injections are sort of forgetful faithful functors]

#todo[functors can also _add_ structure: see, from $cset$ to $cposet$]

#todo[note: _this_ one is faithful]

#todo[in fact, these functors form an _adjunction_; but we'll talk about that later, maybe...]

Given functors $F : cal(C)_1 -> cal(C)_2$ and $G : cal(C)_2 -> cal(C)_3$, we may define their
_composition_ $F ; G$ as follows:
- $|F ; G| = |G| ∘ |F| : |cal(C)_1| → |cal(C)_3|$
- For all $f : cal(C)_1(A, B)$, $(F ; G) med f = G med (F f) : cal(C)_3(G med (F A), G med (F B))$

Furthermore, for an arbitrary category $cal(C)$, we may define the _identity functor_ $id_cal(C)$
as mapping objects and morphisms to themselves. In particular, this equips the set of categories
itself with the structure of a category, the _category of categories_ $ms("Cat")$, as follows:

#definition(name: "Category of categories")[
  The category of categories
  #footnote[
    Again, we actually define the category $ms("Cat")_ℓ$ of $ℓ$-small categories, with
    $ms("Cat")$ corresponding to the category of small categories $ms("Cat")_0$
  ]
  $ms("Cat")$ has
  - Objects $|ms("Cat")|$ categories
  - Morphisms $ms("Cat")(cal(C), cal(D))$ functors $F : cal(C) → cal(D)$
]

#definition(name: "Terminal Object")[
  An object $X : |cal(C)|$ is _terminal_ if for every object $A : |cal(C)|$,
  there exists a _unique_ morphism $!_A : cal(C)(A, X)$.

  We note that terminal objects are unique up to _unique_ isomorphism:
  if $X$ and $X'$ are terminal objects, then $X ≈ X'$.

  Hence, in any $cal(C)$ with a terminal object, we may choose a distinguished terminal object
  $tunit_cal(C) : |cal(C)|$ without loss of generality; where there is no risk of confusion, we
  will often omit the subscript and write $tunit : |cal(C)|$.
  /*
  Dually, an object $tzero_cal(C) : |cal(C)|$ is _initial_ if for every object $A : |cal(C)|$,
  there exists a _unique_ morphism out of it $0_A : cal(C)(tzero_cal(C), A)$.

  We note that terminal and initial objects are unique up to isomorphism;
  that is, if $tunit$ and $tunit'$ are terminal objects, then $tunit ≈ tunit'$, and likewise for
  initial objects.
  //
  Hence we will often speak of "the" terminal object $tunit$ and "the" initial object $tzero$.
  */
]

#definition(name: "Product")[
  Given a family of objects $icol(A) = (A_i | i ∈ I)$ indexed by a set $I$,
  we say that an object $P: |cal(C)|$ is their _product_ if:
  - There exist morphisms $π_i^P : cal(C)(P, A_i)$ such that

  - for each object $X : |cal(C)|$,
    given a family of morphisms $icol(f) = (f_i : cal(C)(X, A_i) | i ∈ I)$,
    there exists a _unique_ morphism $⟨icol(f)⟩^P : cal(C)(X, P)$
    (the _product_ of the $f_i$)
    such that
    $
      ∀ j : I . ⟨icol(f)⟩^P ; π_j = f_j
    $

    That is, for arbitrary $g : cal(C)(X, P)$, we have that
    $
      (∀ j ∈ I . g ; π_j = f_j) <==> g = ⟨icol(f)⟩^P
    $

    Where it is unambiguous from context, we will often omit the superscript $P$ and
    simply write $π_i : cal(C)(P, A_i)$, $⟨icol(f)⟩$.

    Likewise, we will often write $⟨f_i⟩_(i ∈ I)$, $⟨f_i⟩_i$, or $⟨f_1,...,f_n⟩$ for
    $⟨icol(f)⟩^P$ where the meaning is clear from context.

  We note that the product $P$ of a family of objects $A_i$ is unique up to isomorphism;
  that is, if $P$ and $P'$ are products of $A_i$, then $P ≈ P'$.

  In particular, for each family of objects $icol(A) = ( A_i | i ∈ I )$,
  we may choose a distinguished product  $Π icol(A)$ whenever one exists.

  Since an object is the product of the empty family if and only if it is terminal,
  if such a product exists, we may without loss of generality assume that $Π [] = tunit$.
]

In general, where the appropriate products exist, we write

- $Π_(i ∈ I) A_i := Π (A_i | i ∈ I)$.

  Where clear from context, we may omit the subscript and write $Π_i A_i$

- $A × B := Π (lb("l") ↦ A, lb("r") ↦ B)$

- For $n ∈ ℕ$, $A^n := Π (n · [A])$

- Given objects $icol(A) = (A_i | i ∈ I)$ , $icol(B) = (B_i | i ∈ I)$,
  and morphisms $icol(f) = (f_i : cal(C)(A_i, B_i) | i ∈ I)$,
  we define
  $
    Π mb(f) = Π_(i ∈ I)f_i := ⟨π_i^(Π icol(A)) ; f_i⟩_(i ∈ I) : cal(C)(Π icol(A), Π icol(B))
  $

- Likewise, given $f: A_1 → B_1$, $g : A_2 → B_2$, we define
  - $f × g := Π (lb("l") ↦ f, lb("r") ↦ g)$
  - $f × A_2 := f × id_(A_2)$
  - $A_1 × g := id_(A_1) × g$

#todo[every thinning induces a map on the product]

#todo[every permutation, an isomorphism]

#todo[introduce _canonical_ isomorphisms]

#todo[]

/*
In general, if $ι : I → J$ is an injection,
and $icol(A), icol(B)$ are families of objects indexed by $I$ and $J$ respectively,
then there exists a canonical morphism
$
  piinj(icol(A), icol(B), ι)
$
*/

Some important properties of products, where they exist, include:

- $A × B ≈ B × A$, with canonical isomorphisms
  $⟨π_lb("l")^(A × B), π_lb("r")^(A × B)⟩ : A × B -> B × A$ and
  $⟨π_2^(B × A), π_1^(B × A)⟩ : B × A -> A × B$

- $A × tunit ≈ A$, with canonical isomorphisms
  $π_1 : A × tunit → A$ and $⟨id_A, !_A⟩ : A → A × tunit$

  Likewise, $tunit × A ≈ A$.

- $Π (X :: icol(A)) ≈ X × Π icol(A)$, with canonical isomorphims (for $icol(A)$ of length $n$)
  $
    ⟨π_1^(X × Π icol(A)),
      (π_2^(X × Π icol(A)) ; π_1^(Π icol(A))), ..., (π_2^(X × Π icol(A)) ; π_n^(Π icol(A)))⟩
    & : X × Π icol(A) -> Π (X :: icol(A)) \
    ⟨π_1^(Π (X :: icol(A))), ⟨π_(1 + 1)^(Π (X :: icol(A))),...,π_(n + 1)^(Π (X :: icol(A)))⟩⟩
    & : Π (X :: icol(A)) -> X × Π icol(A)
  $

- It follows by induction that $Π (icol(A) lcat icol(B)) ≈ icol(A) lcat icol(B)$

- Likewise, $Π [A] ≈ A$

- $Π [A] ≈ A$, with canonical isomorphisms $π^(Π [A]) : Π [A] → A$ and $⟨id_A⟩ : A → Π [A]$

- In particular, this yields an isomorphism $Π icol(A) × Π icol(B) ≈ Π (icol(A) lcat icol(B))$

- It follows that $A × (B × C) ≈ Π[A, B, C] ≈ (A × B) × C$

- Likewise, $A^m × A^n = A^(n + m)$

#definition(name: "Cartesian Category")[
  A category $cal(C)$ is _cartesian_ if it has all finite products;
  i.e. all products $Π icol(A)$ where $icol(A)$ is finite.

  Note that it suffices for $cal(C)$ to have an initial object and all binary products $A × B$.
]


#definition(name: "Concrete Category")[
  A _concrete category_ $cal(V)$ is a category equipped with a faithful functor
  $U : cal(V) → cset$
]

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

#definition(name: "Concretely Cartesian Category")[
  A concrete category $cal(V)$ is _concretely cartesian_ if it preserves finite products;
  i.e., we have
  $
    ∀ [A_1,...,A_n] . U(Π [A_1,...,A_n]) = Π [U A_1,...,U A_n]
  $
]

For the rest of this thesis,
$cal(V)$ will range over concretely cartesian categories unless otherwise specified.

#definition(name: [$cal(V)$-enriched category])[
  Given a concretely cartesian category $cal(V)$,
  a $cal(V)$-enriched category $cal(C)$, or _$cal(V)$-category_, consists of
  - An set of objects $|cal(C)|$
  - For each pair of objects $A, B : |cal(C)|$, a _hom-object_ $cal(C)(A, B) ∈ |cal(V)|$
  - For each object $A : |cal(C)|$, an _identity morphism_ $id_A : cal(C)(A, B)$
  - For each triple of objects $A, B, C : |cal(C)|$, a _composition morphism_
    $
      (;)_(A, B, C) : cal(V)(cal(C)(A, B) × cal(C)(B, C), cal(C)(A, C))
    $
]

/*
For the rest of this section, we will develop the theory of $cal(V)$-enriched categories in the
special case where $cal(V)$ is concretely cartesian. The general theory of enriched categories is
analogous, but much more complex since we need to deal with coherence conditions, however,
when $cal(V)$ is concretely cartesian, the definitions are essentially the same as in ordinary
category theory. In fact, we can recover the standard category theoretic definitions by noting that
a category is precisely a $cset$-enriched category.
*/

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
  - A mapping on objects $|F| : |cal(C)| → |cal(D)|$
  - For each pair of objects $A, B : |cal(C)|$, a $cal(V)$-morphism
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
  - Objects $|cal(V)ms("Cat")|$ cal(V)-categories
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

== Naturality

#definition(name: [$cal(V)$-natural transformation])[
  Given $cal(V)$-functors $F, G : cal(C) → cal(D)$
  a $cal(V)$-natural transformation $η : F => G$ consists of:
  - For each object $A ∈ |cal(C)|$, a morphism $η_A : cal(D)(F A, G A)$ such that
  - For each morphism $f : cal(C)(A, B)$, we have that
    $
      η_A ; (G med f) = (F med f) ; η_B
    $
    i.e. the following diagram commutes:
    $
      #diagram(cell-size: 15mm, $ F med A edge(η_A, ->) edge("d", F med f, ->) & G med A edge("d", G med f, ->, label-side: #left) \
         F med B edge(η_B, ->, label-side: #right) & G med B $)
    $
]

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
$X_(A_1,...,A_n), Y_(A_1,...,A_n) : |cal(C)|$ parametrized by $n$ objects $A_i : |cal(C)|$
and a family of morphisms
$m_(A_1,...,A_n) : cal(C)(X_(A_1,...,A_n), Y_(A_1,...,A_n))$.
We say that $m$ is _natural_ in $A_i$ if:
- There exists a $cal(V)$-functor $F_i$ such that
  $F_i med B = X_i$

Given a function $|cal(C)|^n → |cal(C)|$
*/

== Coproducts

/*

A coproduct, then, is just the dual notion to a product:

#definition(name: "Coproduct")[
  Given a family of objects $A_i : |cal(C)|$ for some indexing set $I$,
  we say that an object $C: |cal(C)|$ is their _coproduct_ if there exist:
  - Morphisms $ι_i : cal(C)(A_i, C)$ and
  - For each object $X : |cal(C)|$,
    given a family of morphisms $f_i : cal(C)(A_i, X)$ for each $i ∈ I$,
    a _unique_ morphism $[f_i]_(i ∈ I) : cal(C)(C, X)$
    (the _coproduct_ of the $f_i$)
    such that
    $
      ∀ j : I . ι_j ; [f_i]_(i ∈ I) = f_j
    $

    That is, for arbitrary $g : cal(C)(C, X)$, we have that
    $
       (∀ j ∈ I . ι_j ; g = f_j) <==> g = [f_i]_(i ∈ I)
    $

  We note that the coproduct $C$ of a family of objects $A_i$ is unique up to isomorphism;
  that is, if $C$ and $C'$ are coproducts of $A_i$, then $C ≈ C'$.
  Furthermore, an object is the product of the empty family if and only if it is initial.

  We say a category $cal(C)$ is _cocartesian_ if it has _all finite coproducts_;
  i.e. if there exists a function
  $Σ : tlist(|cal(C)|) → |cal(C)|$ such that
  - For $L = [A_1,...,A_n]$, $Σ L$ is a coproduct of $A_i$, and, in particular,
  - $Σ []$ is equal to the initial object $tzero$

  In general, we write
  - $Σ_i A_i := Σ [A_1,...,A_n]$
  - $A + B := Σ [A, B]$
  - For $n ∈ ℕ$, $ntag(n, A) = Σ [A,...,A]$ ($n$ copies of $A$)
  - For morphisms $f_i : cal(C)(A_i, B_i)$ for arbitrary $i ∈ I$,
    - $Σ_i f_i = ⟨f_i ; ι_i⟩_i : Σ_i A_i → Σ_i B_i$, and, therefore, in particular
    - $Σ [f_1,...,f_n] = ⟨f_1 ; ι_1,..., f_n ; ι_n⟩ : Σ [A_1,...,A_n] → Σ [B_1,...,B_n]$
    - $f_1 + f_2 = ⟨f_1 ; ι_1 , f_2 ; ι_2⟩ : A_1 + A_2 → B_1 + B_2$
  - In particular, for $f : cal(C)(A, B)$ and objects $C$, we define
    - $f + C = f + id_C : A + C → B + C$, and
    - $C + f = id_C + f : C + A → C + B$
]

Similarly to products, coproducts satisfy some basic algebraic properties

- $A + B ≈ B + A$

- $A + tzero ≈ A$

- $A + Σ L ≈ Σ (A :: L)$

- $Σ [A] ≈ A$

- $Σ L + Σ L' ≈ Σ (L · L')$

- $A + (B + C) ≈ Σ [A, B, C] ≈ (A + B) + C$

- Likewise, $ntag(m, A) + ntag(n, A) ≈ ntag(m + n, A)$

*/

== Premonoidal Categories

#definition(name: [$cal(V)$-Binoidal Category])[
  A $cal(V)$-binoidal category is a $cal(V)$-category equipped with
  - A function on objects $- ⊗ - : |cal(C)| × |cal(C)| → |cal(C)|$
  - For each object $A : |cal(C)|$, $cal(V)$-functors $A ⊗ -, - ⊗ A : cal(C) → cal(C)$ which
    agree with $- ⊗ -$ on objects

  In general, given $f: A_1 → B_1$ and $g : A_2 → B_2$, we define:
  - $f ⋉ g = f ⊗ A_2 ; B_1 ⊗ g : cal(C)(A_1 ⊗ A_2, B_1 ⊗ B_2)$
  - $f ⋊ g = A_1 ⊗ g ; f ⊗ B_2 : cal(C)(A_1 ⊗ A_2, B_1 ⊗ B_2)$

  We say that a morphism $f$ is _central_ if
  $
    ∀ A_2, B_2 : |cal(C)|, ∀ g : cal(C)(A_2, B_2) . (f ⋉ g = f ⋊ g) ∧ (g ⋉ f = g ⋊ f)
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
  - A distinguished _identity object_ $munit : |cal(C)|$
  - Central natural isomorphisms:
    - $α_(A, B, C) : cal(C)((A ⊗ B) ⊗ C, A ⊗ (B ⊗ C))$ (the _associator_)
    - $λ_A : cal(C)(munit ⊗ A, A)$ (the _left unitor_)
    - $ρ_A : cal(C)(A ⊗ munit, A)$ (the _right unitor_)

  By natural, we mean that $α_(A, B, C)$. $λ_A$, and $ρ_A$ are natural in each of their components;
  i.e., for all morphisms $f: cal(C)(A, A')$, $g: cal(C)(B, B')$, and $h: cal(C)(C, C')$, the following
  _naturality squares_ hold:
  $
    (f ⊗ B) ⊗ C ; α_(A', B, C) & = α_(A, B, C) ; f ⊗ (g ⊗ h) && : cal(C)((A ⊗ B) ⊗ C, A' ⊗ (B ⊗ C)) \
    A ⊗ (g ⊗ C) ; α_(A, B', C) & = α_(A, B, C) ; A ⊗ (g ⊗ h) && : cal(C)((A ⊗ B) ⊗ C, A ⊗ (B' ⊗ C)) \
      A ⊗ B ⊗ h ; α_(A, B, C') & = α_(A, B, C) ; A ⊗ B ⊗ h   && : cal(C)((A ⊗ B) ⊗ C, A ⊗ (B ⊗ C')) \
            munit ⊗ f ; λ_(A') & = λ_A ; f                   && : cal(C)(munit ⊗ A, A') \
            f ⊗ munit ; ρ_(A') & = ρ_A ; f                   && : cal(C)(A ⊗ munit, A')
  $

  Such that the following coherence conditions hold:
  - (Pentagon Identity)
    For all objects $A, B, C, D : |cal(C)|$, the following diagram commutes:
    $
      #diagram($                                 & (A ⊗ B) ⊗ (C ⊗ D) edge("dr", α_(A, B, (C ⊗ D)), ->) &                                \
      ((A ⊗ B) ⊗ C) ⊗ D
      edge("ur", α_((A ⊗ B), C, D), ->)
      edge("d", α_(A, B, C) ⊗ D, ->)  &                                                     &              A ⊗ (B ⊗ (C ⊗ D)) \
      (A ⊗ (B ⊗ C)) ⊗ D
      edge("rr", α_(A, B ⊗ C, D), ->) &                                                     & A ⊗ ((B ⊗ C) ⊗ D)
                                                                                              edge("u", A ⊗ α_(B, C, D), ->) $)
    $

  - (Triangle Identity)
    For all objects $A, B : |cal(C)|$, the following diagram commutes:
    $
      #diagram(cell-size: 15mm, $ (A ⊗ munit) ⊗ B edge(α_(A, munit, B), ->) edge("dr", ρ_A ⊗ id_B, ->, label-side: #right) &
      A ⊗ (munit ⊗ B) edge("d", id_A ⊗ λ_B, ->, label-side: #left) \
      & A ⊗ B $)
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
      For all objects $A, B, C : |cal(C)|$, the following diagram commutes:
      $
        #diagram($ (A ⊗ B) ⊗ C edge(α_(A, B, C), ->) edge("d", σ_(A, B) ⊗ C, ->, label-side: #right) &
        A ⊗ (B ⊗ C) edge(σ_(A, B ⊗ C), ->, label-side: #left) &
        (B ⊗ C) ⊗ A edge("d", α_(B, C, A), ->) \
        (B ⊗ A) ⊗ C edge(α_(B, A, C), ->) &
        B ⊗ (A ⊗ C) edge(B ⊗ σ_(A, C), ->) &
        B ⊗ (C ⊗ A) $)
      $
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

== Monads and Kliesli Categories

#todo[have this as an example of a premonoidal category]

#todo[
  - Introduce the concept of _strength_ via a strong monad
    (later will have strong Elgot structure so this builds intuition)
    - Every monad over $cset$ is strong, so this is often overlooked
  - define a commutative monad; show monoidal $<=>$ commutative
  - notice the subcategory of pure things; think about it
    - return should be monic or it's not faithful; @moggi-89-monad calls this a
      _computational monad_
    - but this is not necessary for our Freyd case
]

= Semantics of #iter-calc()

#todo[
  - Semantics of types
  - Semantics of contexts
  - Semantics of contexts with usage
  - Semantics of
]

= Control-Flow Graphs

<cfgs>

= Future Work

#todo[literally an infinite pile]

#bibliography("refs.bib", style: "acm-edited.csl")

#pagebreak()

#let appendix(body) = {
  set heading(numbering: "A", supplement: [Appendix])
  counter(heading).update(0)
  [ #body <appendix> ]
}

#show: appendix

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
