# PhD Thesis: Categorical Imperative Programming

**Author:** Jad-Elkhaleq Ghalayini, University of Cambridge
**Subtitle:** Type theory, refinement, and semantics for SSA
**Typesetting:** Typst (`typst compile thesis.typ`)
**Target:** 60,000 words

## Topic

Formalizing Static Single Assignment (SSA) form using type theory and category theory. The thesis develops type systems, refinement types, and categorical semantics for SSA-based intermediate representations.

## Structure

- `thesis.typ` — main entry point, includes all chapters
- `thesis-template.typ` — formatting template
- `syntax.typ` — custom math notation and macros
- `refs.bib` — bibliography

### Chapters (in order)

1. **Introduction** — `thesis.typ` (inline)
2. **Static Single Assignment** — `content/static-single-assignment.typ`
3. **Conventions and Notation** — `content/background/conventions.typ`
4. **Type-Theoretic SSA** — `content/type-theoretic-ssa/inductive-ssa.typ`
5. **Substructural SSA** — `content/type-theoretic-ssa/substructural-ssa.typ`
6. **Basic Enriched Category Theory** — `content/background/category-theory.typ`
7. **Semantics of Imperative Programming** — `content/semantics/imperative.typ`
   - Subfiles: `cart-expr.typ`, `cart-region.typ`, `cart-ssa.typ`
8. **Appendix**

### Supporting files

- `content/rules/` — typing rules (`hasty.typ`, `types.typ`, `intro.typ`, `haslb.typ`)
- `snippets.typ` — code snippet definitions
- `todos.typ` — TODO tracking utilities

## Key Typst packages

- `wordometer` (word count), `lemmify` (theorems), `curryst` (proof trees),
  `fletcher` (diagrams), `simplebnf` (BNF grammars)

## Conventions

- Thesis is work-in-progress; many sections have TODOs
- Papers and LaTeX sources to be added later for reference
