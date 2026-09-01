// Editorial tracking and migration utilities.

// Global todo counter (auto-increments per call).
// Each todo is a labelled metadata entry queryable via `typst query`.

#let todo-counter = counter("todo")

#let todo(body, kind: "task", owner: "author", source: none, visible: true) = {
  todo-counter.step()
  [#metadata((kind: kind, owner: owner, source: source, body: body)) <todo>]
  if visible { context {
    let n = todo-counter.get().first()
    text(fill: red, weight: "bold", size: 0.85em)[
      TODO #n (#kind, #owner): #body
    ]
  } }
}

// Keep the taxonomy deliberately small. These wrappers make ownership and
// intent queryable without forcing imported drafts into a detailed workflow.
#let question(body, owner: "author", source: none) = todo(
  body, kind: "question", owner: owner, source: source,
)
#let suggestion(body, owner: "author", source: none) = todo(
  body, kind: "suggestion", owner: owner, source: source,
)
#let plan(body, owner: "author", source: none) = todo(
  body, kind: "plan", owner: owner, source: source,
)
#let error(body, owner: "agent", source: none) = todo(
  body, kind: "error", owner: owner, source: source,
)

// Mark notation which is preserved from an imported paper pending migration.
// The body renders unchanged; metadata powers `make status` and gives the old
// syntax an explicit removal criterion.
#let old-syntax(body, family: "unclassified", note: none) = {
  [#metadata((family: family, note: note)) <old-syntax>]
  body
}
