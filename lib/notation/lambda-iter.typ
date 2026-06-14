// Notation for the λ_iter expression language.
//
// Mirrors the surface syntax used in the paper (the `\let`, `\case`, `\iter`,
// injection, abort, and quantity macros). Kept in one place so the rendering
// of every λ_iter term can be tweaked from here.

// Keyword styling: sans-serif, matching `\ms{...}` from the paper.
#let kw(name) = $sans(#name)$

// --- Types ---
#let tyunit = $bold(1)$   // unit type
#let tyempty = $bold(0)$  // empty type
#let tytensor = $⊗$       // tensor product
#let tysum = $+$          // coproduct

// --- Expressions ---

// Coproduct injections: ι_l a and ι_r b.
#let linl(a) = $iota_l med #a$
#let linr(b) = $iota_r med #b$

// Abort (eliminator of the empty type): abort a.
#let labort(a) = $#kw("abort") med #a$

// The arrow separating a pattern from a branch body. In the paper `\lto` is
// rendered as a colon; isolate it here so it is easy to change.
#let lto = $:$

// Let-binding: let x = a; b. The binder `x` may itself be a pattern, e.g.
// `(x, y)`, so this covers both ordinary and destructuring lets.
#let letx(x, a, b) = $#kw("let") med #x = #a; med #b$

// Case-expression: case e { ι_l x : a, ι_r y : b }.
#let casex(e, x, a, y, b) = $#kw("case") med #e med {linl(#x) lto #a, linr(#y) lto #b}$

// Iteration: iter a { ι_r x : b } -- a tail-controlled loop.
#let iterx(a, x, b) = $#kw("iter") med #a med {linr(#x) lto #b}$

// --- Quantities ---
// The join-semilattice of usage quantities Q^0 = {0, 1, 1^?, ω^+, ω}.
#let zeroq = $0$        // used zero times
#let oneq = $1$         // used exactly once
#let delq = $1^?$       // used at most once (0 ⊔ 1)
#let cpyq = $omega^+$   // used one or more times
#let topq = $omega$     // used any number of times
