#import "../../syntax.typ": *

#let rtl-flat-grammar = figure(
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
          Or[$c$][_constant_]
          Or[$(V)$][_structure_]
        }),
        Prod($V$, {
          Or[$·$][]
          Or[$V, fexpr(lb("f"), v)$][]
        }),
      ),
      bnf(
        Prod($β$, {
          Or[$x = o seq β$][_assign_]
          Or[$(icol(x)) = o seq β$][_destructure_]
          Or[$τ$][_terminator_]
        }),
        Prod($icol(x)$, {
          Or[$·$][]
          Or[$icol(x), fexpr(lb("f"), x)$][]
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
      := (fexpr(lb("[0]"), x_0),..., fexpr(lb("[n - 1]"), x_(n - 1)))
      /*
      quad
      "where"
      quad
      lpi = π_0,
      rpi = π_1
      */
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
)

#rtl-flat-grammar

#let ssa-flat-grammar = figure(
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
          Or[$c$][_constant_]
          Or[$(V)$][_structure_]
        }),
        Prod($V$, {
          Or[$·$][]
          Or[$V, fexpr(lb("f"), v)$][]
        }),
      ),
      bnf(
        Prod($β$, {
          Or[$x = o seq β$][_assign_]
          Or[$(V) = o seq β$][_destructure_]
          Or[$τ$][_terminator_]
        }),
        Prod($icol(x)$, {
          Or[$·$][]
          Or[$icol(x), fexpr(lb("f"), x)$][]
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
)

#ssa-flat-grammar

#let lex-ssa-op-grammar = figure(
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
)

#lex-ssa-op-grammar

#let ssa-expr-grammar = figure(
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
            Or[$c$][_constant_]
            Or[$f med e$][_application_]
            Or[$lb("l") med e$][_label_]
            Or[$(E)$][_structure_]
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
)

#ssa-expr-grammar

#let lex-ssa-grammar = figure(
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
)

#lex-ssa-grammar

#let tt-ssa-grammar = figure(
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
)

#tt-ssa-grammar

#let rtl-10-fact = subpar.grid(
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

#rtl-10-fact
