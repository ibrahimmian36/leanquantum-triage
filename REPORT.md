# LeanQuantum `ForMathlib/` triage

Prepared for Robert Rand / the inQWIRE group by Millennium Research
(Ibrahim Mian, Shayaan Siddique). Everything below is relative to pinned
revisions, and every claim traces to a file or command in the
accompanying repo that you can re-run.

**Pins.** LeanQuantum `44fc4eb1` (main, 2026-05-15); mathlib `c1e30e17`
(2026-04-23, the revision in your `lake-manifest.json` — your `lakefile.lean`
requires mathlib with no pinned revision, so the manifest is the only record
of what actually builds); toolchain `leanprover/lean4:v4.30.0-rc2`.

**What we did.** We enumerated all 89 declarations in
`Quantumlib/ForMathlib/` (machine-generated inventory in
`inventory/inventory.tsv`), searched mathlib at your pinned revision and Lean
core at your pinned toolchain for each, and classified every declaration into
exactly one of four buckets. Every REDUNDANT claim is backed by
`evidence/Redundant.lean`, a file that imports **only mathlib**, restates your
lemma verbatim, and closes it from mathlib/core alone — if it didn't compile,
we didn't call it redundant. The evidence file's axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`.

## The immediate win: 20 declarations you can delete today

Mathlib or Lean core already provides all of the following. The branch
`triage/delete-redundant` removes them, and we verified the result by
building, not by estimating: all 29 modules compile on the branch except
`Computation.lean`, which fails identically on your untouched `main` (see
the observations at the end), so every module known to compile at your pin
still compiles with the deletions applied.

### Unitary closure lemmas (`Matrix/Unitary.lean`) — all five, currently unused in the repo

| Yours | Upstream replacement |
|---|---|
| `mul_of_isUnitary` | `mul_mem` (`unitaryGroup` is a submonoid) |
| `conjTranspose_of_isUnitary` | `Unitary.star_mem` (with `Matrix.star_eq_conjTranspose`) |
| `transpose_of_isUnitary` | `Matrix.transpose_mem_unitaryGroup_iff.mpr` |
| `smul_of_isUnitary` | `Unitary.smul_mem_of_mem` |
| `kron_of_isUnitary` | `Matrix.kronecker_mem_unitary` + a mechanical `reindex` transport (spelled out in `evidence/Redundant.lean`) |

`kronecker_mem_unitary` landed in mathlib's `LinearAlgebra/UnitaryGroup.lean`
and is exactly the Kronecker-of-unitaries fact on the `Fin m × Fin n` index
type; your `kron` is its reindex along `finProdFinEquiv`.

### The `lsbs` layer (`BitVec/Basic.lean`, `BitVec/Lemmas.lean`)

`lsbs` is definitionally `x.setWidth w`, and Lean core already has the whole
lemma family under `setWidth` names — most of them `@[simp]` in core:

| Yours | Lean core |
|---|---|
| `cons_msb_lsbs` | `BitVec.cons_msb_setWidth` |
| `lsbs_zero` | `BitVec.setWidth_zero` |
| `lsbs_cons` | `BitVec.setWidth_cons` |
| `lsbs_xor` / `lsbs_or` / `lsbs_and` | `BitVec.setWidth_xor` / `_or` / `_and` |
| `getElem_eq_msb` | `BitVec.msb_eq_getLsbD_last` + `BitVec.getLsbD_eq_getElem` |

Renaming `lsbs` to `setWidth` at use sites (Pauli files, `PowBitVec`) lets all
eight declarations go.

### `Fintype (BitVec w)` — declared twice, needed zero times

Both instances (`BitVec/Basic.lean:19` and the verbatim duplicate at
`BitVec/Lemmas.lean:10`) are found by instance search from mathlib's
`FinEnum (BitVec n)` (`Mathlib/Data/FinEnum.lean`) through the priority-100
`FinEnum → Fintype` instance. As written, your build has three `Fintype`
instances for `BitVec` in scope; the local ones shadow mathlib's with a
different (defeq-incompatible) `Finset.univ`, which is the classic setup for
`decide`/`Fintype.card` proofs breaking on import-order changes.

### The rest

| Yours | Upstream replacement |
|---|---|
| `Matrix.conjTranspose_transpose_comm` | `Matrix.conjTranspose_transpose` + `Matrix.transpose_conjTranspose` (both sides are `M.map star`) |
| `Matrix.pow_true`, `Matrix.pow_false` | `Bool.toNat_true`/`_false` + `pow_one`/`pow_zero` (all `@[simp]`; also, the statements need only `Monoid`, not matrices over a `CommRing`) |
| `CMatrix.Commute` | definitional alias of `_root_.Commute` |
| `Fin.add_neg` | `(sub_eq_add_neg a b).symm` (the `n = 0` case is vacuous) |

Two near-misses worth knowing about. `Complex.exp_three_pi_div_two` is
derivable from mathlib in two rewrites (`exp_add` + `exp_two_pi_mul_I` +
`exp_neg_pi_div_two_mul_I`) and `Complex.one_ne_neg_one` is a `norm_num`
one-liner (general form: `Ring.neg_one_ne_one_of_char_ne_two`) — the
compiling derivations for both are in the evidence file. But we classify both
KEEP rather than delete: `Data/Gate/Equivs.lean:86` silently depends on the
first as a `@[simp]` normal form, and `Data/Gate/Pauli/Lemmas.lean:20`
(`σy_ne_1`) on the second, and we verified empirically that deleting either
breaks the build. They earn their keep.

The deletion branch is a strict delete-and-rename with one disclosed
exception: `weight_and_le`'s proof needed a three-line adjustment, because the
original proof relied on `lsbs` being opaque to `simp`, and the rename to the
(simp-transparent) core `setWidth` changed which goals `simp` closes. The
replacement instantiates the induction hypothesis and finishes with `omega`,
which is robust to simp-set drift.

## Worth upstreaming: 7 declarations — but 4 of them target Lean core, not mathlib

A finding that reshapes the BitVec half of this directory:
`Mathlib/Data/BitVec.lean` says, verbatim, *"Please do not extend this file
further: material about BitVec needed in downstream projects can either be
PR'd to Lean, or kept downstream if it also relies on Mathlib."* So pure
BitVec material goes to `leanprover/lean4`, not mathlib.

**To Lean core** (drafted in `upstream/Lean4_BitVec_Lemmas.lean`):
`cons_true_allOnes`; `lsbs_allOnes` generalized to
`setWidth_allOnes (h : k ≤ n) : (allOnes n).setWidth k = allOnes k`;
`and_xor_distrib_left` and `and_xor_distrib_right`.

**To mathlib** (drafted in `upstream/Mathlib_Complex_*.lean`):
`Complex.cos_pi_div_four` and `Complex.sin_pi_div_four` (mathlib has the
`Real` versions and the `Complex` family stops at `π/2`), and
`Complex.neg_I_pow_eq_pow_mod` (the `-I` companion of mathlib's
`I_pow_eq_pow_mod`).

## Genuinely yours: 37 declarations stay (LOCAL)

The `CMatrix`/`CVector`/`CSquare` abbreviations, the global `π` notation, the
`IsUnitary` abbrev (mathlib's idiom is membership in `Matrix.unitaryGroup`),
`powBitVec` and its lemmas (quantum-specific), and all of `Kron.lean`: your
`kron` is a `Fin`-flattened wrapper around mathlib's `kroneckerMap`, and every
mathematical fact it transports (`add`, `smul`, `one`, `mul_kron_mul`,
`assoc`, `trace`, `det`, `inv`, `conjTranspose`) already exists in mathlib on
the `l × m` index type — the wrapper itself is a legitimate project choice, so
the transport layer stays with it.

## Judgment calls we did not make for you: the `weight`/`dot` cluster and `AntiCommute`

**`BitVec.weight`, `dot`, `dotZ₂`, `foldl` and their 20 lemmas.** At your
pinned toolchain these are genuine gaps — no popcount for `BitVec` exists in
core or mathlib. But the ground is moving under this cluster: current Lean
core master has grown `BitVec.cpop : BitVec w → BitVec w` (population count,
with `clz`/`ctz`, a bitblasting circuit for `bv_decide`, and 32 lemmas —
`cpop_zero`, `cpop_allOnes`, `cpop_cons`, `cpop_append`, … are your
`weight_zero`, `weight_allOnes`, `weight_cons` in `cpop` form). So at your
next toolchain bump, `weight` itself becomes a wrapper (`(x.cpop).toNat`),
and re-deriving your base lemmas from core's will shrink this file again.

What core does **not** have, even on master, is the part you actually built
for QEC: the boolean algebra of popcount (`weight_or` inclusion–exclusion,
`weight_and_le`, `weight_and_self`) and the GF(2) pairing (`dot`, `dotZ₂`,
distributivity over `^^^`). That is the genuinely novel, genuinely
upstreamable core of this cluster — and its natural home is a Lean core PR
stated in `cpop` terms, riding the active `cpop` work. We'd be glad to draft
the Zulip message proposing it, credited to inQWIRE, for your approval.

**`CMatrix.AntiCommute`.** Mathlib has `Commute` but no anticommutation
anywhere — a real gap, and fundamental to Pauli algebra. If proposed it should
be stated for a general ring (`a * b = -(b * a)`), with enough API to justify
the definition. Since nothing in LeanQuantum uses it yet, this one is worth a
Zulip temperature-check rather than a PR.

## Tally

| Bucket | Count |
|---|---|
| REDUNDANT (delete; verified by compiling evidence + green deletion branch) | 20 |
| UPSTREAM (4 → Lean core, 3 → mathlib; drafts in `upstream/`, unopened) | 7 |
| LOCAL (stays) | 37 |
| UNCLEAR (design questions we'd put to Zulip/you) | 25 |

Observations in passing, all verified against the pin:

1. **Part of the library is invisible to `lake build`.** The root
   `Quantumlib.lean` imports only `Basic` and `Data.Error.Operator`, and the
   default build compiles just what's reachable from there. Outside that
   graph — never compiled by a plain `lake build` — are
   `ForMathlib/Data/Fin.lean`, `ForMathlib/Data/Matrix/Unitary.lean`,
   `Data/Gate/Unitary.lean`, `Data/Gate/ConjTranspose.lean`,
   `Data/Gate/Hermitian.lean`, `Data/Gate/Lemmas.lean`, and
   `Computation.lean`. We compiled the first four successfully on untouched
   `main` (Hermitian and Gate/Lemmas we compiled on the deletion branch);
   `Computation.lean` is already broken at your own pin — three
   "No goals to be solved" errors at 33:27 (`EPRpair_create`'s
   `fin_cases i <;> (simp; rfl)`: simp now closes three of the four cases
   outright, so the `rfl` has nothing left to do; replacing the `rfl` with
   `try rfl` should fix it, though we have not run that fix). We verified
   the failure is byte-identical on untouched `main` and on our deletion
   branch, so it predates and is unrelated to the deletions — invisible rot
   of exactly the kind a default `lake build` cannot catch. Importing these
   files from the root (or widening the lakefile globs) closes the gap.
2. `Data/Error/Operator.lean:138` contains a `sorry` (surfaced as a warning
   in the default build).
3. `ForMathlib/Data/Matrix/PowBitVec.lean` imports `Quantumlib.Tactic.Basic`,
   which appears unused there; dropping it would make `ForMathlib/`
   self-contained.
4. `lakefile.lean`'s unpinned mathlib requirement is why every mathlib move
   can break the build — pinning to the manifest revision would make
   toolchain bumps a choice rather than an event.
