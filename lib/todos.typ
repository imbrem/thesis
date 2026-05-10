// TODO tracking, margin notes, word count utilities.

// Global todo counter (auto-increments per call).
// Each todo is a labelled metadata entry queryable via `typst query`.

#let todo-counter = counter("todo")

#let todo(body) = {
  todo-counter.step()
  [#metadata(body) <todo>]
  context {
    let n = todo-counter.get().first()
    text(fill: red, weight: "bold", size: 0.85em)[TODO #n: #body]
  }
}
