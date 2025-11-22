#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/simplebnf:0.1.1": *

#import "@preview/wordometer:0.1.5": word-count, total-words
#show: word-count.with(exclude: <no-wc>)

#let max-words = 60000
#let percent-done = context {
  calc.round(decimal((100 * state("wordometer").final().words) / max-words), digits: 3)
}
#let p-doom = context { 
  let prop-done = state("wordometer").final().words / max-words
  if prop-done > 0.9 {
    [*LOW*]
  } else if prop-done > 0.5 {
    [*MEDIUM*]
  } else {
    [*HIGH*]
  }
}

#import "thesis-template.typ": *
#import "todos.typ": todo, todo-inline, total-todos

#let ms(txt) = $sans(txt)$
#let mb(txt) = $bold(txt)$

#set text(lang: "en")

#set document(
  title: [Categorical imperative programming: 
    a type theory and denotational semantics for Static Single Assignment (SSA) form]
)

#title()

#align(center + horizon)[
  #todo("make a title page; preferably as a template")
]

#align(center + horizon)[
  *The current word count is* $#total-words slash #max-words ≈ #percent-done%$ complete.

  *There are $#total-todos$ TODOs remaining*

  $P(ms("doom"))$ is currently *#p-doom*
]

#pagebreak()

#statement-of-originality

#todo[What's the right way to format this?] 

#todo[Do we put the acknowledgements here or after the abstract?]

#pagebreak()

#align(center + horizon)[
  Is _this_ abstract enough?
  #todo[Actually write an abstract]
]

#pagebreak()

#outline()

#pagebreak()

= Introduction

#todo[start at the middle]

= Static Single Assignment (SSA)

== From Three Address Code to SSA

#todo[$n$-ary or binary presentation?]

Directly optimizing a source language can be difficult, 
  because surface languages are often very large and have features 
    (such as type inference and overloading) 
  which make it difficult to express sound program equivalences. 
Elaborating a surface language to a simpler intermediate representation makes it easier to write program analyses and optimizations. 
One of the earliest compiler IRs introduced is _register transfer language_ (_RTL_) @allen-70-cfa,
  commonly referred to as _three-address code_.

#let ite(o, l, r) = $ms("if") #o thick { #l } ms("else") { #r }$
#let linl(v) = $ι_l med #v$
#let linr(v) = $ι_r med #v$
#let labort(v) = $ms("abort") #v$
#let seq = $; thick$
#let casestmt2(o, vl, bl, vr, br) = $ms("case") #o thick {linl(vl) : #bl seq linr(vr) : #br}$
#let brb(ℓ, v) = $ms("br") #ℓ thick #v$
#let retb(v) = $ms("ret") #v$

RTL programs consists of a _control-flow graph_ (CFG) $G$ 
  with a distinguished, nameless entry block. 
Each node of the CFG corresponds to a _basic block_ $β$, 
  which is a straight-line sequence of _instructions_ $x = f(y, z)$ 
    (hence the name _3-address code_, referring to the typical three variables $x, y, z$) 
  followed by a _terminator_ $τ$, 
    which can be a (conditional) branch to another basic block. 
We give a grammar for 3-address code in Figure~#todo-inline[3-address grammar], 
  with some slight adjustments to the usual presentation:

#todo[introduce destructures more smoothly? consider $n$-ary case?]

  #todo[mention that case statements can also be nested?]

- _Constants_ $c$ are interpreted as nullary instructions $c()$.
- _Conditional branches_ $ite(x, τ, τ')$ are desugared to 
    case-statements $casestmt2(x, y, τ, z, τ')$ on a Boolean $x : mb(1) + mb(1)$. 
  This is equivalent in power to regular conditional branches, 
    while allowing our work to generalize easily to higher-level settings as well.
- _Return statements_ $retb(v)$ are desugared to branches $brb(ℓ_ms("exit"), v)$ 
    to a distinguished exit label $ℓ_ms("exit")$. 
  In particular, 
    this allows a return-statement to appear in the branch of a case-statement or if-statement.

#figure(
  [
    #stack(
      dir: ltr,
      spacing: 3em,
      bnf(
        Prod(
          $v$,
          annot: $ms("Val")$,
          {
            Or[$x$][_variable_]
            Or[$(v, v')$][_tuple_]
            Or[$()$][_unit_]
          }
        )
      ),
      bnf(
        Prod(
          $o$,
          annot: $ms("Inst")$,
          {
            Or[$v$][_value_]
            Or[$f med v$][_operation_]
            Or[$linl(v)$][_left injection_]
            Or[$linr(v)$][_right injection_]
            Or[$labort(v)$][_abort_]
          }
        )
      )
    )
    #stack(
      dir: ltr,
      spacing: 3em,
      bnf(
        Prod(
          $β$,
          annot: $ms("BB")$,
          {
            Or[$x = o seq β$][_assign_]
            Or[$(x, y) = o seq β$][_destructure_]
            Or[$τ$][_terminator_]
          }
        )
      ),
      bnf(
        Prod(
          $τ$,
          annot: $ms("Trm")$,
          {
            Or[$brb(ℓ, o)$][_branch_]
            Or[$casestmt2(o, x, τ, y, τ')$][_case_]
          }
        )
      )
    )
    #bnf(
      Prod(
        $β$,
        annot: $ms("CFG")$,
        {
          Or[$β$][_entry block_]
          Or[$G seq ℓ : β$][_labeled basic block_]
        }
      )
    )
  ],
  caption: [Grammar for RTL],
  kind: image
)

/*
Directly optimizing a source language can be difficult, because surface languages are often
very large and have features (such as type inference and overloading) which make it difficult
to express sound program equivalences. Elaborating a surface language to a simpler intermediate
representation makes it easier to write program analyses and optimizations. One of the earliest
compiler IRs introduced is \emph{three-address code}~\cite{allen-70-cfa} (also
known as \emph{register transfer language (RTL)}). 

3-address programs consists of a \emph{control-flow graph} (CFG) $G$ with a distinguished, nameless
entry block. Each node of the CFG corresponds to a \emph{basic block} $\beta$, which is a
straight-line sequence of \emph{instructions} $x = f(y, z)$ (hence the name \emph{3-address code},
referring to the typical three variables $x, y, z$) followed by a \emph{terminator} $\tau$, which
can be a (conditional) branch to another basic block. We give a grammar for 3-address code in
Figure~\ref{fig:3addr-grammar}, with some slight adjustments to the usual presentation:
\begin{itemize}
  \item \emph{Constants} $c$ are interpreted as nullary instructions $c()$.

  \item \emph{Conditional branches} $\ite{x}{\tau}{\tau'}$ are desugared to case-statements
  $\casestmt{x}{y}{\tau}{z}{\tau'}$ on a sum type $x : \mb{1} + \mb{1}$. This is equivalent in power
  to regular conditional branches, while allowing our work to generalize easily to higher-level
  settings as well.

  Furthermore, we allow case-statements (and hence if-statements) in a terminator to be
  \emph{nested}, allowing us to emulate switch-statements $\ms{switch}(o) \{c_1 : \tau_1 ,
  ... , c_n : \tau_n\}$ as nested case-statements. This does not add any additional
  expressive power, but avoids the proliferation of intermediate basic-blocks.

  \item \emph{Return statements} $\ms{ret}\;v$ are desugared to branches $\brb{\ell_{\ms{exit}}}{v}$
  to a distinguished exit label $\ell_{\ms{exit}}$. In particular, this allows a return-statement to
  appear in the branch of a case-statement or if-statement.
\end{itemize}

\begin{figure}[H]
  \begin{center}
    \begin{grammar}
      <\(v\)> ::= \(x\) \;|\; \((v, v')\) \;|\; \(()\)

      <\(o\)> ::= \(v\) \;|\; \(f\;v\) \;|\; \(\linl{v}\) \;|\; \(\linr{v}\) \;|\; \(\labort{v}\)

      <\(\beta\)> ::=
      \(x = o ; \beta\)
      \;|\; \((x, y) = o ; \beta\)
      \;|\; \(\tau\)

      <\(\tau\)> ::= \(\brb{\ell}{o}\) \;|\; $\casestmt{o}{y}{\tau}{z}{\tau'}$

      <\(G\)> ::= \(\beta\) \;|\; \(G \;\; \ell : \beta\)
    \end{grammar}
  \end{center}
  \caption{Grammar for 3-address code}
  \Description{}
  \label{fig:3addr-grammar}
\end{figure}

As a concrete example, consider the simple imperative program to compute $10!$ given in
Figure~\ref{fig:fact-program}. We can normalize our code into 3-address code, as in
Figure~\ref{fig:fact-3addr}, by:
\begin{itemize}
  \item Converting structured control flow (e.g., \ms{while}) into unstructured jumps between basic
  blocks labelled \ms{start}, \ms{loop}, and \ms{body}.
  \item Converting composite expressions like $a * (i + 1)$ into a sequence of definitions naming each
  subexpression.
\end{itemize}

\begin{figure}
  \begin{subfigure}[t]{.5\textwidth}
    \begin{align*}
      & \ms{let}\;n = 10; \\
      & \ms{let\;mut}\;i = 1; \\
      & \ms{let\;mut}\;a = 1; \\
      & \ms{while}\;i < n\;\{ \\
      & \quad a = a * (i + 1) \\
      & \quad i = i + 1; \\
      & \} \\
      & \ms{ret}\;a \\
    \end{align*}
    \caption{As an imperative program}
    \label{fig:fact-imp}
  \end{subfigure}%
  \begin{subfigure}[t]{.5\textwidth}
    \begin{align*}
      %\ms{start}:\quad
                        & n = 10; \\
                        & i = 1; \\
                        & a = 1; \\
                        & \ms{br}\;\ms{loop} \\
      \ms{loop}: \quad  & \ms{if}\;i < n\;
                          \{\;\ms{br}\;\ms{body}\;\}\;
                          \ms{else}\;\{\;\ms{ret}\;a\;\} \\
      \ms{body}: \quad  & t = i + 1; \\
                        & a = a * t; \\
                        & i = i + 1; \\
                        & \ms{br}\;\ms{loop}
    \end{align*}
    \caption{As 3-address code}
    \label{fig:fact-3addr}
  \end{subfigure}
  \caption{
    A simple, slightly suboptimal program to compute $10!$ via multiplication in a loop, represented
    as typical imperative code and in 3-address code.
  }
  \Description{}
  \label{fig:fact-program}
\end{figure}

While functional languages typically rely on \emph{lexical scoping}, where the scope of a variable
is determined by its position within the code's nested structure, 3-address code uses a different
scoping mechanism based on \emph{dominance}. In particular, a variable $x$ is considered to be in
scope at a specific point $P$ if and only if all execution paths from the program's entry point to
$P$ pass through a definition $D$ for $x$. In this case, we say that the definition $D$
\emph{dominates} $P$. The relation on basic blocks ``$A$ dominates $B$" can in fact be viewed as a
tree rooted at the entry block: every pair of basic blocks $A, B$ have a least common ancestor $C$
which dominates them both; we call this tree the \emph{dominator tree} \cite{cytron-ssa-intro-91}.

Even though three address code was designed to simplify flow analysis, many optimizations remain
difficult to express in this format. Because a variable's value may be set by multiple definitions
throughout the program's execution, variables do not have stable values, and so it is not in general
safe to substitute a definition for a variable. To improve our ability to reason about programs, we
introduce the \emph{static single assignment} restriction, originally proposed by
\citet{alpern-ssa-original-88}, which states that every variable must be defined at exactly one
point in the program. Because there is a unique definition for each variable, substitution is valid.

We can we  intuitively think of each variable as being defined by an immutable \ms{let}-binding, and
a variable $x$ is in scope at a program point $P$, if and only if it sunique definition site $D_x$
strictly dominates $P$.

A given basic block can be converted to SSA form by numbering each definition of a variable,
effectively changing references to $x$ to references to $x_t$, i.e. ``$x$ at time $t$.'' For
example, we could rewrite
\begin{equation*}
\begin{array}{lcl}
  x = 3y + 5; & & \letexpr{x_0}{3y + 5}{}  \\
  x = 3x + 2; & \qquad \approx \qquad & \letexpr{x_1}{3x_0 + 2} \\
  \ms{ret}\;(3x + 1) & & \ms{ret}\;(3x_1 + 1)
\end{array}
\end{equation*}
This transformation enables algebraic reasoning about expressions involving each $x_t$. However,
since we can only define a variable once in SSA form, expressing programs with loops and branches
becomes challenging. For example, na\"ively trying to lower the program in
Figure~\ref{fig:fact-3addr} into SSA form would not work, since the reference to $i$ in the
right-hand-side of the statement $i = i + 1$ can refer to \emph{either} the previous value of $i$
from the last iteration of the loop \emph{or} the original value $i = 1$. The classical solution is
to introduce \emph{$\phi$-nodes}, which select a value based on the predecessor block from which
control arrived. We give the lowering of our program into SSA with $\phi$-nodes in
Figure~\ref{fig:fact-ssa}.

\citet{cytron-ssa-intro-91} introduced the first efficient algorithm to lower a program in 3-address
code to valid SSA while introducing a minimum number of $\phi$-nodes, making SSA practical for
widespread use as an intermediate representation. Unfortunately, $\phi$-nodes do not have an obvious
operational semantics.

Additionally, they require us to adopt more complex scoping rules than simple
dominance-based scoping. For example, in the basic block \ms{loop} in Figure~\ref{fig:fact-ssa},
$i_0$ evaluates to 1 if we came from \ms{start} and to $i_1$ if we came from \ms{body}. Similarly,
$a_0$ evaluates to either 1 or $a_1$ based on the predecessor block. This does not obey
dominance-based scoping, since $i_0$ and $i_1$ are defined \emph{after} the $\phi$-nodes $i_0$,
$a_0$ that reference them, which seems counterintuitive -- after all, variables are typically used
after they are defined. In fact, since the value of a $\phi$-node is determined by which basic block
is our immediate predecessor, we instead need to use the rule that expressions in $\phi$-node
branches with source $S$ can use any variable $y$ defined at the \emph{end} of $S$. Note that this
is a strict superset of the variables visible for a normal instruction $x$, which can only use
variables $y$ which \emph{dominate} $x$ -- i.e., such that \emph{every} path from the entry block to
the definition of $x$ goes through $y$, rather than only those paths which also go through $S$.

\begin{figure}
  \begin{subfigure}[t]{.5\textwidth}
    \begin{align*}
      %\ms{start}:\quad
                        & n = 10; \\
                        & i = 1; \\
                        & a = 1; \\
                        & \ms{br}\;\ms{loop} \\
      \ms{loop}: \quad  & \ms{if}\;i < n\;
                          \{\;\ms{br}\;\ms{body}\;\}\;
                          \ms{else}\;\{\;\ms{ret}\;a\;\} \\
      \ms{body}: \quad  & \ms{let}\;t = i + 1; \\
                        & a = a * t; \\
                        & i = i + 1; \\
                        & \ms{br}\;\ms{loop}
    \end{align*}
    \caption{3-address code}
  \end{subfigure}%
  \begin{subfigure}[t]{.5\textwidth}
    \begin{align*}
      %\ms{start}:\quad
                        & \ms{let}\;n = 10; \\
                        & \ms{br}\;\ms{loop} \\
      \ms{loop}: \quad  & \ms{let}\;i_0 = \phi(\ms{start}: 1, \ms{body}: i_1) \\
                        & \ms{let}\;a_0 = \phi(\ms{start}: 1, \ms{body}: a_1) \\
                        & \ms{if}\;i_0 < n\;
                          \{\;\ms{br}\;\ms{body}\;\}\;
                          \ms{else}\;\{\;\ms{ret}\;a_0\;\} \\
      \ms{body}: \quad  & \ms{let}\;t = i_0 + 1 \\
                        & \ms{let}\;a_1 = a_0 * t \\
                        & \ms{let}\;i_1 = i_0 + 1 \\
                        & \ms{br}\;\ms{loop}
    \end{align*}
    \caption{Converted to SSA form}
    \label{fig:fact-ssa}
  \end{subfigure}
  \caption{
    Conversion of three address code for the program in Figure~\ref{fig:fact-program} to SSA
    form, requring the insertion of $\phi$-nodes for $i$ and $a$ due to control-flow dependent
    updates. Note how SSA-form can be viewed as ``three address code in which all
    \ms{let}-bindings are immutable.''
  }
  \Description{}
\end{figure}

While this rule can be quite confusing, and in particular makes it non-obvious how to assign an
operational semantics to $\phi$-nodes, the fact that the scoping for $\phi$-node branches is based
on the source block, rather than the block in which the $\phi$-node itself appears, hints at a
possible solution. By \emph{moving} the expression in each branch to the \emph{call-site}, we can
transition to an isomorphic syntax called basic blocks with arguments (BBA), as illustrated in
Figure \ref{fig:fact-bba}. In this approach, each $\phi$-node -- since it lacks side effects and has
scoping rules independent of its position in the basic block, depending only on the source of each
branch -- can be moved to the top of the block. This reorganization allows us to treat each
$\phi$-node as equivalent to an argument for the basic block, with the corresponding values passed
at the jump site. Converting a program from BBA format back to standard SSA form with $\phi$-nodes
is straightforward: introduce a $\phi$-node for each argument of a basic block, and for each branch
corresponding to the $\phi$-node, add an argument to the jump instruction from the appropriate
source block. We give a formal grammar for basic blocks-with-arguments SSA in
Figure~\ref{fig:bba-grammar}
\footnote{ Many variants of SSA do not allow variables to appear alone
  on the right-hand side of assignments, such as
  $x = y; \beta$.  We do not
  incorporate this restriction, though we could by
  normalizing even further and substituting $[y/x]\beta$ instead.
}
. Note that this grammar no longer needs a separate terminator for
returns: we can treat the return point as a distinguished label (with argument) that a program can
jump to.

\begin{figure}[H]
  \begin{center}
    \begin{grammar}
      <\(v\)> ::= \(x\) \;|\; \((v, v')\) \;|\; \(()\)

      <\(o\)> ::= \(v\) \;|\; \(f\;v\) \;|\; \(\linl{v}\) \;|\; \(\linr{v}\) \;|\; \(\labort{v}\)

      <\(\beta\)> ::=
      \(\letstmt{x}{o}{\beta}\)
      \;|\; \(\letstmt{(x, y)}{o}{\beta}\)
      \;|\; \(\tau\)

      <\(\tau\)> ::= \(\brb{\ell}{v}\) \;|\; $\casestmt{x}{y}{\tau}{z}{\tau'}$

      <\(G\)> ::= \(G \;\; \ell(x) : \beta\) \;|\; \(\beta\)
    \end{grammar}
  \end{center}
  \caption{Grammar for basic blocks-with-arguments SSA}
  \Description{}
  \label{fig:bba-grammar}
\end{figure}

This allows us to use dominance-based scoping without any special cases for $\phi$-nodes.
When considering basic blocks, this means that a variable is visible within the block $D$ where it
is defined, starting from the point of its definition. It continues to be visible in all subsequent
blocks $P$ that are strictly dominated by $D$ in the control-flow graph (CFG). For example, in
Figure~\ref{fig:fact-bba}:
\begin{itemize}
  \item \ms{start} strictly dominates \ms{loop} and \ms{body}; thus, the variable $n$ defined in
  \ms{start} is visible in \ms{loop} and \ms{body}.
  \item \ms{loop} strictly dominates \ms{body}; therefore, the parameters $i_0$, $a_0$ to \ms{loop}
  are visible in \ms{body} without the need to pass them as parameters.
  \item \ms{body} does \emph{not} strictly dominate \ms{loop}, since there is a path from \ms{start}
  to \ms{loop} that does not pass through \ms{body}.
\end{itemize}

\begin{figure}
  \begin{subfigure}[t]{.5\textwidth}
    \centering
    \begin{align*}
      %\ms{start}:\quad
                        & \ms{let}\;n = 10; \\
                        & \ms{br}\;\ms{loop} \\
      \ms{loop}: \quad  & \begingroup \color{red}
                          \ms{let}\;i_0 = \phi(\ms{start}: 1, \ms{body}: i_1)
                          \endgroup \\
                        & \begingroup \color{blue}
                          \ms{let}\;a_0 = \phi(\ms{start}: 1, \ms{body}: a_1)
                          \endgroup \\
                        & \ms{if}\;i_0 < n\;\{\;\ms{br}\;\ms{body}\;\} \\
                        & \ms{else}\;\{\;\ms{ret}\;a_0\;\} \\
      \ms{body}: \quad  & \ms{let}\;t = i_0 + 1 \\
                        & \ms{let}\;a_1 = a_0 * t \\
                        & \ms{let}\;i_1 = i_0 + 1 \\
                        & \ms{br}\;\ms{loop}
    \end{align*}
    \caption{With $\phi$-nodes}
    \label{fig:fact-phi}
  \end{subfigure}%
  \begin{subfigure}[t]{.5\textwidth}
    \centering
    \begin{align*}
      %\ms{start}:\quad
                                  & \ms{let}\;n = 10; \\
                                  & \ms{br}\;\ms{loop}(\textcolor{red}{1}, \textcolor{blue}{1}) \\
      \ms{loop}(\textcolor{red}{i_0}, \textcolor{blue}{a_0}): \quad
                                  & \ms{if}\;i_0 < n\; \{\;\ms{br}\;\ms{body}\;\} \\
                                  & \ms{else}\;\{\;\ms{ret}\;a_0\;\} \\
      \ms{body}: \quad            & \ms{let}\;t = i_0 + 1 \\
                                  & \ms{let}\;a_1 = a_0 * t \\
                                  & \ms{let}\;i_1 = i_0 + 1 \\
                                  & \ms{br}\;\ms{loop}(\textcolor{red}{i_1}, \textcolor{blue}{a_1})
                                  \\ \\
    \end{align*}
    \caption{Basic-blocks with arguments}
    \label{fig:fact-bba}
  \end{subfigure}

  \caption{
    The program in Figure \ref{fig:fact-program} written in standard SSA (using $\phi$ nodes),
    like in LLVM \cite{llvm}, and in basic-blocks with arguments SSA, like in MLIR \cite{mlir} and
    Cranelift \cite{cranelift}. The arguments $i_0, a_0$ corresponding to the $\phi$-nodes $i_0,
    a_0$ are colored in \textcolor{red}{red} and \textcolor{blue}{blue}, respectively.
  }
  \Description{}
\end{figure}
*/

== Type-theoretic SSA

= Type-Theoretic SSA

#todo[TOPLAS + refinement here]

= Refinement

#todo[TOPLAS + refinement here]

= Lowering to SSA

#todo[λiter ↔ Type Theoretic SSA]

#todo[Type Theoretic SSA ⊇ ANF]

#todo[ANF ⊇ Lexical SSA]

#todo[⇒ λiter ↔ Lexical SSA]

#todo[Lexical SSA ↔ Graph SSA]

= Denotational Semantics of SSA

#todo[TOPLAS + refinement here]

= Simple Models of SSA

#todo[Partiality]

#todo[Nondeterminism]

#todo[Elgot monad transformers]

#todo[Heaps and printing]

= Verified Optimizations

#todo[the basics: CSE, GVN, DCE, SCCP, peephole @siddharth-24-peephole]

#todo[E-graphs @cranelift]

#todo[Vectorization]

#todo[`mem2reg`]

= Memory Models for SSA

== Brookes Models

#todo[Brookes-style @brookes-96-sc-abstract concurrency models]

== Interaction Trees and Choice Trees

#todo[ITrees @xia-20-itrees and CTrees @chappe-25-ctrees]

== Trace Models

#todo[Stream actions, pomsets, and TSO]

= Future Work

#todo[literally an infinite pile]

#bibliography("refs.bib")
