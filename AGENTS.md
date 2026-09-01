# Agent guidance

Read `CLAUDE.md` for the repository layout, build commands, and thesis-authoring
constraints. In particular, do not add generated prose to the thesis outside a
`#todo[...]` unless the user explicitly asks for prose.

## Research workflow

This repository deliberately supports multiple related formalizations in
parallel. Do not prematurely force all experiments through one representation
or one abstraction layer.

Parallel developments are encouraged when they expose different proof or API
tradeoffs, including:

- named, locally nameless, de Bruijn, and intrinsically typed syntax;
- a no-subtyping core, minimal `0 <= A <= 1` subtyping, and richer
  proof-relevant subtyping;
- direct monadic and abstract categorical semantics;
- extrinsic and intrinsic typing;
- executable models and universal categorical constructions.

Keep each experiment in a clear namespace and folder. Share genuinely stable
components—types, signatures, categorical infrastructure, and theorem
statements—but do not introduce a complicated common abstraction merely to
eliminate short-term duplication. Record explicit comparison maps and
agreement theorems between variants.

When one experiment becomes the preferred presentation, preserve useful
alternatives until their comparison theorem and migration path are known.

## Agent delegation

For substantial formalization tasks, split independent work across agents and
separate worktrees when concurrency is available. Good boundaries include:

- alternate syntax or typing designs;
- semantic interfaces and concrete instances;
- metatheory versus categorical structure;
- implementation versus theorem/API audit.

Agents working in parallel must avoid editing the same worktree files. Use
small compiling commits, report exact theorem scope, and never claim a result
from filenames or intended architecture alone.

## Lean standards

- The active project is `formalization/thesis/`.
- Reference formalizations under `formalization/papers/` are implementation
  archaeology, not automatically authoritative APIs.
- Build focused modules while developing, then run `lake build Isotope` before
  handoff.
- New completed modules must contain no `sorry`, `admit`, placeholder axioms,
  or unjustified `unsafe` declarations.
- Preserve proof relevance where it is mathematically intended. If a result
  assumes semantic proof irrelevance—for example for subtype witnesses—state
  that assumption in an explicit optional typeclass rather than silently
  collapsing the base syntax.
- Prefer theorem-level bridges between variants over informal claims that two
  developments coincide.

## Git and PRs

Use separate branches/PRs for independent experiments. Draft PRs are welcome
for compiling research artifacts whose design is not yet settled. State:

- what is proved;
- what is merely defined or explored;
- which build command passed;
- remaining placeholders or blockers;
- dependencies on other experimental branches.

Do not merge competing experiments solely to reduce branch count. Merge shared
infrastructure first, then rebase or retarget dependent work after its API is
stable.
