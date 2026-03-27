# GitHub Actions

## Branches

- **`outputs`**: Orphan branch storing compiled artifacts. Structure mirrors the repo.
- **`gh-pages`**: Deployed from `outputs` branch by `deploy.yml`. Index page is rendered from `README.md` via pandoc.

## Workflows

- **`deploy.yml`** ("Build and Deploy"): Runs on push to `main`. Four-job DAG: `typst`, `latex`, and `formalization` build in parallel, then `deploy` (which `needs` all three) pushes PDFs to `outputs` and deploys to GitHub Pages.
- **`thesis.yml`** ("Compile Typst"): PR check only. Compiles all `.typ` files in `thesis/` and `notes/`.
- **`papers.yml`** ("Compile LaTeX"): PR check only. Compiles LaTeX papers.
- **`formalization-ci.yml`** ("Formalization CI"): PR check only. Builds Lean 4 project.
- **`formalization-update.yml`**: Manual-dispatch workflow to update mathlib dependency.

## Conventions

- No third-party deploy actions for pushing to branches — use raw git commands.
- PDFs (small artifacts) go to the `outputs` branch, preserving directory structure.
- Lean docs (large artifacts) are uploaded as workflow artifacts and assembled at deploy time.
