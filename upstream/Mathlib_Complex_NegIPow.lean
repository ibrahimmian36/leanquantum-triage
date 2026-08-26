/-
UPSTREAM CANDIDATE — DO NOT OPEN A PR.
Mathematics by the INQWIRE group (inQWIRE/LeanQuantum, MIT license,
Quantumlib/ForMathlib/Data/Complex/Basic.lean).  Authorship and whether to
upstream at all are Rand's call; this file only demonstrates the
mathlib-ready shape.

Target file: Mathlib/Data/Complex/Basic.lean, next to
`Complex.I_pow_eq_pow_mod` (line ~612 at pin c1e30e17).

The `-I` companion of `I_pow_eq_pow_mod`.  LeanQuantum's proof already
uses only mathlib lemmas and is reproduced verbatim (it is their proof,
not ours).
-/
import Mathlib.Data.Complex.Basic

namespace Complex

/-- `(-I) ^ n` is periodic in `n` with period 4, like `I ^ n`
(`Complex.I_pow_eq_pow_mod`). -/
theorem neg_I_pow_eq_pow_mod (n : ℕ) : (-I) ^ n = (-I) ^ (n % 4) := by
  rw [neg_pow, neg_pow Complex.I, ← Complex.I_pow_eq_pow_mod]
  congr 1
  simp [show 4 = 2 * 2 by rfl, -Nat.reduceMul,
        Nat.mod_mul, pow_add, pow_mul,
        ← neg_one_pow_eq_pow_mod_two]

end Complex
