#let refinement-factorial-figure() = [#figure([
  #grid(
    columns: (1fr, 1fr, 1fr),
    column-gutter: 0.8em,
    [#figure([
      #text(size: 7.5pt)[#grid(
        columns: (auto, auto), column-gutter: 0.5em, row-gutter: 0.12em,
        [$sans("start"):$], $sans("let") med n = 10;$,
        [], $sans("br") med sans("loop");$,
        [$sans("loop"):$], text(fill: red)[$sans("let") med i_0 = phi.alt(sans("start"): 1, sans("body"): i_1);$],
        [], text(fill: blue)[$sans("let") med a_0 = phi.alt(sans("start"): 1, sans("body"): a_1);$],
        [], $sans("if") med i_0 < n med {sans("br") med sans("body")}$,
        [], $sans("else") med {sans("ret") med a_0};$,
        [$sans("body"):$], $sans("let") med t = i_0 + 1$,
        [], $sans("let") med a_1 = a_0 times t$,
        [], $sans("let") med i_1 = i_0 + 1$,
        [], $sans("br") med sans("loop")$,
      )]],
      caption: [$phi.alt$-nodes],
    ) <refall:fig:fact-phi>],
    [#figure([
      #text(size: 7.5pt)[#grid(
        columns: (auto, auto), column-gutter: 0.5em, row-gutter: 0.12em,
        [$sans("start"):$], $sans("let") med n = 10;$,
        [], [$sans("br") med sans("loop")(#text(fill: red)[$1$], #text(fill: blue)[$1$]);$],
        [$sans("loop")(#text(fill: red)[$i_0$], #text(fill: blue)[$a_0$]):$], $sans("if") med i_0 < n med {sans("br") med sans("body")}$,
        [], $sans("else") med {sans("ret") med a_0};$,
        [$sans("body"):$], $sans("let") med t = i_0 + 1$,
        [], $sans("let") med a_1 = a_0 times t$,
        [], $sans("let") med i_1 = i_0 + 1$,
        [], [$sans("br") med sans("loop")(#text(fill: red)[$i_1$], #text(fill: blue)[$a_1$])$],
      )]],
      caption: [Basic-blocks with arguments],
    ) <refall:fig:fact-bba>],
    figure([
      #text(size: 7.5pt)[#grid(
        columns: (auto,), row-gutter: 0.12em,
        [$sans("let") med n = 10;$],
        [$sans("br") med sans("loop")(#text(fill: red)[$1$], #text(fill: blue)[$1$]);$],
        [$sans("where") med sans("loop")(#text(fill: red)[$i_0$], #text(fill: blue)[$a_0$]): {$],
        [#h(1em)$sans("if") med i_0 < n med {sans("br") med sans("body")}$],
        [#h(1em)$sans("else") med {sans("ret") med a_0};$],
        [#h(1em)$sans("where") med sans("body"): {$],
        [#h(2em)$sans("let") med t = i_0 + 1$],
        [#h(2em)$sans("let") med a_1 = a_0 times t$],
        [#h(2em)$sans("let") med i_1 = i_0 + 1$],
        [#h(2em)$sans("br") med sans("loop")(#text(fill: red)[$i_1$], #text(fill: blue)[$a_1$])$],
        [#h(1em)$}$], [$}$],
      )]],
      caption: [Lexical scoping],
    ),
  )
], caption: [
  A program to compute $10 !$ written in standard SSA (using $phi.alt$
  nodes), like in LLVM #cite(<llvm>), and using basic-blocks with arguments,
  like in MLIR #cite(<mlir>) and Cranelift #cite(<cranelift>), with both implicit
  (dominance-based) and explicit (lexical) scoping. The arguments
  $i_0 \, a_0$ corresponding to the $phi.alt$-nodes $i_0 \, a_0$ are
  colored in red and blue, respectively.
]) <refall:fig:fact-lex>]
