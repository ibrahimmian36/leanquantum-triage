# leanquantum-triage

A declaration-by-declaration triage of `Quantumlib/ForMathlib/` in
[inQWIRE/LeanQuantum](https://github.com/inQWIRE/LeanQuantum): for each of
its 89 declarations, decide whether it is already provided upstream
(REDUNDANT), belongs upstream (UPSTREAM), should stay in the project
(LOCAL), or is a genuine judgment call (UNCLEAR) — with machine-checked
evidence for every REDUNDANT claim.

The deliverable is [`REPORT.md`](REPORT.md). The mathematics in
`ForMathlib/` is the inQWIRE group's; this repository only classifies it.
Nothing here has been PR'd anywhere, and any upstreaming is inQWIRE's call,
including authorship.

By Millennium Research (Ibrahim Mian, Shayaan Siddique).

## Pins

Every claim in this repository is stated relative to:

| What | Value |
|---|---|
| LeanQuantum commit | `44fc4eb1f4ba512e659deacd3468fda0a764d162` (main, 2026-05-15) |
| mathlib revision | `c1e30e172c8fda21e6776bf1f10351e882ee31b9` (2026-04-23, the revision in LeanQuantum's `lake-manifest.json`; the lakefile itself tracks mathlib HEAD with no pin) |
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` |

## Layout

- `REPORT.md` — the triage report: what can be deleted (with upstream
  replacements), what is worth upstreaming and where, what should stay, and
  the open design questions. Final tally: 20 REDUNDANT / 7 UPSTREAM /
  37 LOCAL / 25 UNCLEAR.
- `evidence/Redundant.lean` — the proof behind every deletion claim. It
  imports **only Mathlib**, restates each REDUNDANT declaration verbatim
  (checked mechanically by `inventory/diff_statements.py`), and closes it
  from mathlib/core alone. `evidence/axiom-audit.txt` is the recorded
  `#print axioms` output: every proof's closure is within
  `{propext, Classical.choice, Quot.sound}`.
- `inventory/` — two independent inventories of `ForMathlib/` that agree
  exactly: `gen_inventory.py` → `inventory.tsv` (source scan) and
  `DumpDecls.lean` → `env-decls.tsv` (compiled-environment dump), plus
  `classification.tsv`, the per-declaration verdicts with evidence pointers.
- `upstream/` — compiling, upstream-shaped drafts for the UPSTREAM bucket
  (three files: two targeting mathlib, one targeting Lean core). Deliberately
  unsubmitted: whether and how to upstream, and under whose names, is
  inQWIRE's decision.
- `leanquantum-deletion-branch.bundle` — a git bundle of LeanQuantum
  containing `main` at the pin and the `triage/delete-redundant` branch,
  which removes all 20 REDUNDANT declarations (renaming the project's `lsbs`
  to core's `setWidth` at use sites). Verification logs:
  `deletion-build.log` (every module that compiles on `main` still compiles
  on the branch) and `baseline-computation.log` (the one failing module,
  `Computation.lean`, fails identically on pristine `main` — a pre-existing
  issue, documented in the report).

## Reproduce

Everything re-runs from the bundle (needs ~10 GB of disk for the mathlib
build cache, and elan):

```
git clone leanquantum-deletion-branch.bundle LeanQuantum
cd LeanQuantum
git checkout 44fc4eb1f4ba512e659deacd3468fda0a764d162
lake exe cache get
lake build
lake env lean ../evidence/Redundant.lean
```

Then check out `triage/delete-redundant` and rebuild to reproduce the
deletion-branch verification. The mathlib revision is pinned by the
committed `lake-manifest.json`; do not run `lake update`.
