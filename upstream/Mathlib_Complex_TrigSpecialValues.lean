/-
UPSTREAM CANDIDATE — DO NOT OPEN A PR.
Mathematics by the INQWIRE group (inQWIRE/LeanQuantum, MIT license,
Quantumlib/ForMathlib/Data/Complex/Basic.lean).  Authorship and whether to
upstream at all are Rand's call; this file only demonstrates the
mathlib-ready shape.

Target file: Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean
(the `Complex` section, next to `Complex.cos_pi_div_two` /
`Complex.sin_pi_div_two`; the `Real` versions `Real.cos_pi_div_four` and
`Real.sin_pi_div_four` already exist at lines ~714/721).

Names below follow the existing mathlib pattern `cos_pi_div_four`.
LeanQuantum marks both `@[simp]`; the Real versions in mathlib are not
`@[simp]`, so the attribute should be dropped for consistency unless a
maintainer asks otherwise.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Complex

open Real

theorem cos_pi_div_four : Complex.cos (π / 4) = √2 / 2 := by
  rw [show ((π : ℂ) / 4) = ((π / 4 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Real.cos_pi_div_four]
  norm_cast

theorem sin_pi_div_four : Complex.sin (π / 4) = √2 / 2 := by
  rw [show ((π : ℂ) / 4) = ((π / 4 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sin, Real.sin_pi_div_four]
  norm_cast

end Complex
