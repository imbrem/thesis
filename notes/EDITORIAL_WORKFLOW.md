# Editorial convergence workflow

This workflow manages decisions and proof claims without generating thesis
prose. The author remains responsible for every replacement paragraph.

## Two queues

- Put document-local work in a structured `#todo`: use `kind`, `owner`,
  `audience`, `source`, `status`, `priority`, `target`, and `lean` only to the
  extent useful. TODO metadata is queryable and may be hidden with
  `visible: false`.
- Put chapter-ordering decisions and cross-cutting formalization questions in
  `notes/editorial-queue.json`. These notes never render in the thesis.

Keep the taxonomy small. Prefer `question`, `suggestion`, `potential-plan`,
`error`, and `task`; ownership/audience handles who should respond. Resolve an
item by changing its status to `decided` or `deferred`, recording the decision
as a new field, and retaining the original question for history.

## Short author loop

1. Run `make queue`. Resolve one critical/high decision, or explicitly defer it.
2. Choose a leaf Typst source and run:

   ```sh
   python3 scripts/thesis.py review --file thesis/path/to/section.typ
   ```

3. Answer the five prompts, edit the displayed source block, then run the
   printed command for the next block. The tool displays existing source but
   never proposes replacement prose.
4. When a block makes a mechanization claim, cite an exact active declaration
   in a TODO/queue record. `partial`, `interface-only`, and `paper-only` are not
   interchangeable with proved.
5. Build the leaf, then the chapter. At chapter boundaries run `make status`,
   `make lint`, `make queue`, and `make thesis`.

The queue's evidence check proves only that cited files/declaration names still
exist. It does not inspect theorem types, assumptions, axioms, or whether a
theorem matches nearby thesis prose. Those checks require source review plus a
fresh Lean build and `#print axioms` transcript for selected capstones.
