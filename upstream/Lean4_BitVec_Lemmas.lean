/-
UPSTREAM CANDIDATE — DO NOT OPEN A PR.
Mathematics by the INQWIRE group (inQWIRE/LeanQuantum, MIT license,
Quantumlib/ForMathlib/Data/BitVec/Lemmas.lean).  Authorship and whether to
upstream at all are Rand's call; this file only demonstrates shape.

TARGET IS LEAN CORE (leanprover/lean4, Init/Data/BitVec/Lemmas.lean), NOT
mathlib: Mathlib/Data/BitVec.lean says explicitly "Please do not extend this
file further: material about BitVec needed in downstream projects can either
be PR'd to Lean, or kept downstream if it also relies on Mathlib."

These four are the small, `lsbs`-free BitVec facts LeanQuantum proves that
core does not have at v4.30.0-rc2.  Statements are generalized to core
spelling (`setWidth` instead of the project-local `lsbs`, general width where
the original was width-specialized).  Proofs here use mathlib-flavored tactics
for convenience; core PRs would need core-only proofs (`Nat.*`/`omega`/`ext`),
which is mechanical.
-/
import Mathlib

namespace BitVecUpstream
open BitVec

/-- Companion to core's `msb_allOnes`/`getMsbD_allOnes`: prepending `true`
to `allOnes m` gives `allOnes (m + 1)`.  LeanQuantum: `cons_true_allOnes`. -/
theorem cons_true_allOnes : cons true (allOnes m) = allOnes (m + 1) := by
  ext
  simp [getElem_cons, getElem_allOnes]

/-- Truncating `allOnes` gives `allOnes` (generalizes LeanQuantum's
`lsbs_allOnes`, which is the case `n = m + 1`, `k = m`). -/
theorem setWidth_allOnes (h : k ≤ n) : (allOnes n).setWidth k = allOnes k := by
  ext i hi
  simp [getElem_setWidth]
  omega

/-- `&&&` distributes over `^^^` on the left (bitwise
`Bool.and_xor_distrib_left`).  LeanQuantum: `and_xor_distrib_left`. -/
theorem and_xor_distrib_left (x y z : BitVec w) :
    x &&& (y ^^^ z) = x &&& y ^^^ x &&& z := by
  ext
  simp [Bool.and_xor_distrib_left]

/-- `&&&` distributes over `^^^` on the right.  LeanQuantum:
`and_xor_distrib_right`. -/
theorem and_xor_distrib_right (x y z : BitVec w) :
    (x ^^^ y) &&& z = x &&& z ^^^ y &&& z := by
  ext
  simp [Bool.and_xor_distrib_right]

end BitVecUpstream
