# Formalization audit status

- Milestone: theorem-level legacy claim audit complete (source audit); clean
  historical builds and `#print axioms` transcripts are deferred to toolchain
  restoration.
- Last green commit: pending this audit commit.
- Audited revisions: `discretion` `624b878a`; `debruijn-ssa` `316bd9a6`;
  `sparky` `82d782a8`; `refined-ssa` `956ba420`.
- Exact source-audit commands: `rg -n` over all Lean declarations and paper
  claims; `git submodule status`; `git log -1`; targeted `sed` inspection of
  every declaration cited in `formalization/CLAIM_AUDIT.md`.
- Exact attempted build commands: `lake build` in
  `formalization/papers/debruijn-ssa`; `elan run
  leanprover/lean4:v4.15.0-rc1 lake --version`. Both fail because the installed
  toolchain has no `lake` executable. `lean --version` succeeds at v4.15.0-rc1.
- Remaining holes: clean builds and capstone `#print axioms` output; these are
  explicitly marked in the matrix and require the restoration work.
- Claim mismatches: generic denotation and semantic soundness are paper-only;
  categorical initiality is only partially represented by syntactic
  packing/unpacking; the published SPARC-TSO mechanization claim is contradicted
  by the audited `sparky` snapshot; refinement soundness/completeness and
  interconversion are paper-only.
- Author decisions required: none for the audit. Future prose must choose
  whether to narrow the historical mechanization claims or complete the missing
  developments.
