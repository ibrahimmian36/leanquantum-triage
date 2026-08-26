/-
REDUNDANT-bucket evidence file for the LeanQuantum ForMathlib triage.

Rules of this file:
* It imports ONLY Mathlib (which re-exports Lean core, where `BitVec` lives).
* Every declaration classified REDUNDANT is restated here VERBATIM (same
  statement, same hypotheses, same namespaces) and closed using only
  Mathlib/core declarations.  `inventory/diff_statements.py` checks the
  verbatim claim mechanically.  (`exp_three_pi_div_two` and `one_ne_neg_one` also appear, marked
  DERIVABLE-BUT-KEEP: derivable from mathlib, but retained in LeanQuantum
  because Gate proofs use them as simp lemmas.)
* Local `def`/`abbrev`/`notation` copied from LeanQuantum appear solely so the
  statements can be written verbatim; they are marked [copied] below.  No
  evidence proof uses another evidence lemma.
* Pins: LeanQuantum 44fc4eb1f4ba512e659deacd3468fda0a764d162,
  mathlib c1e30e172c8fda21e6776bf1f10351e882ee31b9 (from lake-manifest.json),
  toolchain leanprover/lean4:v4.30.0-rc2.

Each lemma's docstring names the upstream replacement.
-/
import Mathlib

set_option maxHeartbeats 400000

/-! ### [copied] statement-forming definitions from LeanQuantum

Copied verbatim from `Quantumlib/ForMathlib/Data/Complex/Basic.lean`,
`.../Matrix/Basic.lean`, `.../Matrix/Kron.lean`, `.../Matrix/Unitary.lean`,
`.../BitVec/Basic.lean` so the statements below can be written exactly as in
the source.  None of these names exist in mathlib at the pin, so declaring
them in their real namespaces collides with nothing.
-/

notation "π" => Real.pi

abbrev CMatrix m n := Matrix (Fin m) (Fin n) ℂ
abbrev CSquare n := CMatrix n n

abbrev Matrix.IsUnitary {n} (M : CSquare n) := M ∈ Matrix.unitaryGroup (Fin n) ℂ

def Matrix.kron (m₁ : CMatrix a b) (m₂ : CMatrix c d) : CMatrix (a * c) (b * d) :=
  Matrix.of fun x y => m₁ x.divNat y.divNat * m₂ x.modNat y.modNat

scoped[Kron] infixl:100 " ⊗ " => Matrix.kron

def BitVec.lsbs (x : BitVec (w + 1)) : BitVec w := x.setWidth w

/-! ### `Quantumlib/ForMathlib/Data/BitVec/Basic.lean` and `.../Lemmas.lean` -/

namespace BitVec

/-- REDUNDANT: instance search finds this from Mathlib's
`FinEnum (BitVec n)` (Mathlib/Data/FinEnum.lean) through the priority-100
instance `FinEnum → Fintype`.  Declared twice in LeanQuantum
(BitVec/Basic.lean:19 and BitVec/Lemmas.lean:10). -/
example : Fintype (BitVec w) := inferInstance

/-- REDUNDANT: core `BitVec.cons_msb_setWidth` (`@[simp]` in
Init/Data/BitVec/Bootstrap.lean), since `lsbs x` unfolds to `x.setWidth w`. -/
theorem cons_msb_lsbs (x : BitVec (w + 1)) :
  cons x.msb x.lsbs = x := BitVec.cons_msb_setWidth x

/-- REDUNDANT: core `BitVec.setWidth_zero`. -/
theorem lsbs_zero :
  (0#(m + 1)).lsbs = 0#m := BitVec.setWidth_zero m (m + 1)

/-- REDUNDANT: core `BitVec.setWidth_cons`. -/
theorem lsbs_cons (x : BitVec w) b :
  (BitVec.cons b x).lsbs = x := BitVec.setWidth_cons

/-- REDUNDANT: core `BitVec.setWidth_xor`. -/
theorem lsbs_xor (x y : BitVec (w + 1)) :
  (x ^^^ y).lsbs = x.lsbs ^^^ y.lsbs := BitVec.setWidth_xor

/-- REDUNDANT: core `BitVec.setWidth_or`. -/
theorem lsbs_or (x y : BitVec (w + 1)) :
  (x ||| y).lsbs = x.lsbs ||| y.lsbs := BitVec.setWidth_or

/-- REDUNDANT: core `BitVec.setWidth_and`. -/
theorem lsbs_and (x y : BitVec (w + 1)) :
  (x &&& y).lsbs = x.lsbs &&& y.lsbs := BitVec.setWidth_and

/-- REDUNDANT: core `BitVec.msb_eq_getLsbD_last` with
`BitVec.getLsbD_eq_getElem`. -/
theorem getElem_eq_msb (x : BitVec (w + 1)) : x[w] = x.msb := by
  rw [BitVec.msb_eq_getLsbD_last, Nat.add_sub_cancel,
      BitVec.getLsbD_eq_getElem (by omega)]

end BitVec

/-! ### `Quantumlib/ForMathlib/Data/Complex/Basic.lean` -/

namespace Complex

/-- DERIVABLE-BUT-KEEP (classified LOCAL): `norm_num` closes it; the general
fact is `Ring.neg_one_ne_one_of_char_ne_two` (ℂ has characteristic zero).
Kept in LeanQuantum anyway: `Data/Gate/Pauli/Lemmas.lean:20` (`σy_ne_1`)
silently depends on it as a `@[simp]` lemma (deleting it breaks that build;
verified empirically on the deletion branch). -/
theorem one_ne_neg_one : (1 : ℂ) ≠ -1 := by norm_num

/-- DERIVABLE-BUT-KEEP (classified LOCAL): provable from `Complex.exp_add`
with the dedicated special values `Complex.exp_two_pi_mul_I` and
`Complex.exp_neg_pi_div_two_mul_I` (both `@[simp]` in Mathlib), via
`3π/2 = 2π + (-π/2)` — the proof below is that derivation.  Kept in
LeanQuantum anyway: `Data/Gate/Equivs.lean:86` silently depends on it as a
`@[simp]` normal form (deleting it breaks that build; verified empirically
on the deletion branch). -/
theorem exp_three_pi_div_two : Complex.exp (3 * ↑π / 2 * Complex.I) = -Complex.I := by
  rw [show (3 : ℂ) * ↑π / 2 * Complex.I
        = 2 * ↑π * Complex.I + -↑π / 2 * Complex.I by ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul,
      Complex.exp_neg_pi_div_two_mul_I]

end Complex

/-! ### `Quantumlib/ForMathlib/Data/Fin.lean` -/

namespace Fin

/-- REDUNDANT: `sub_eq_add_neg` for the `AddCommGroup (Fin (n+1))` instance;
the `n = 0` case is vacuous (`Fin 0` is empty). -/
theorem add_neg (a b : Fin n) : a + -b = a - b := by
  cases n
  · exact a.elim0
  · exact (sub_eq_add_neg a b).symm

end Fin

/-! ### `Quantumlib/ForMathlib/Data/Matrix/Basic.lean` -/

namespace Matrix

/-- REDUNDANT: `Matrix.conjTranspose_transpose` and
`Matrix.transpose_conjTranspose` (both sides are `M.map star`; also `rfl`). -/
theorem conjTranspose_transpose_comm : ∀ (A : CMatrix m n),
  Aᴴᵀ = Aᵀᴴ := fun A =>
    (Matrix.conjTranspose_transpose A).trans (Matrix.transpose_conjTranspose A).symm

/-- REDUNDANT: `Bool.toNat_true` + `pow_one`; needs only `[Monoid M]`,
not a matrix or `CommRing` at all. -/
theorem pow_true [Fintype n] [DecidableEq n] [CommRing R] (M : Matrix n n R) :
    M ^ true.toNat = M := by rw [Bool.toNat_true, pow_one]

/-- REDUNDANT: `Bool.toNat_false` + `pow_zero`; needs only `[Monoid M]`. -/
theorem pow_false [Fintype n] [DecidableEq n] [CommRing R] (M : Matrix n n R) :
    M ^ false.toNat = 1 := by rw [Bool.toNat_false, pow_zero]

/- `CMatrix.Commute` is definitionally `_root_.Commute`
(`def CMatrix.Commute (A B : CMatrix n n) : Prop := _root_.Commute A B`),
so it is REDUNDANT by inspection; there is nothing separate to prove. -/

end Matrix

/-! ### `Quantumlib/ForMathlib/Data/Matrix/Unitary.lean` -/

open Kron

namespace Matrix

/-- REDUNDANT: `Matrix.transpose_mem_unitaryGroup_iff`. -/
theorem transpose_of_isUnitary : ∀ (M : CSquare n),
  M.IsUnitary → Mᵀ.IsUnitary := fun _ h =>
    Matrix.transpose_mem_unitaryGroup_iff.mpr h

/-- REDUNDANT: `Unitary.star_mem` (star of a matrix is `Mᴴ`, by
`Matrix.star_eq_conjTranspose`). -/
theorem conjTranspose_of_isUnitary : ∀ (M : CSquare n),
  M.IsUnitary → Mᴴ.IsUnitary := fun M h =>
    Matrix.star_eq_conjTranspose M ▸ Unitary.star_mem h

/-- REDUNDANT: `mul_mem` for the submonoid `Matrix.unitaryGroup`. -/
theorem mul_of_isUnitary : ∀ (M₁ M₂ : CSquare n),
  M₁.IsUnitary → M₂.IsUnitary → (M₁ * M₂).IsUnitary := fun _ _ h₁ h₂ =>
    mul_mem h₁ h₂

/-- REDUNDANT: `Unitary.smul_mem_of_mem`. -/
theorem smul_of_isUnitary : ∀ (c : ℂ) (M : CSquare n),
  M.IsUnitary → c ∈ unitary ℂ → (c • M).IsUnitary := fun _ _ hM hc =>
    Unitary.smul_mem_of_mem hc hM

open Kronecker in
/-- REDUNDANT in substance: `Matrix.kronecker_mem_unitary` (in Mathlib's
LinearAlgebra/UnitaryGroup.lean) is exactly this fact on the `Fin m × Fin n`
index type; LeanQuantum's `kron` is its transport across
`reindex finProdFinEquiv finProdFinEquiv`, and the transport is mechanical
(`Matrix.conjTranspose_reindex`, `Matrix.submatrix_mul_equiv`,
`Matrix.submatrix_one_equiv`). -/
theorem kron_of_isUnitary : ∀ (M₁ : CSquare m) (M₂ : CSquare n),
  M₁.IsUnitary → M₂.IsUnitary → (M₁ ⊗ M₂).IsUnitary := by
  intro M₁ M₂ h₁ h₂
  have hk := Matrix.kronecker_mem_unitary h₁ h₂
  rw [Unitary.mem_iff] at hk
  have hdef : M₁ ⊗ M₂
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (M₁ ⊗ₖ M₂) := rfl
  have hstar : star (M₁ ⊗ M₂)
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (star (M₁ ⊗ₖ M₂)) := by
    rw [hdef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
        ← Matrix.star_eq_conjTranspose]
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [hstar, hdef, Matrix.reindex_apply, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv, hk.1, Matrix.submatrix_one_equiv]
  · rw [hstar, hdef, Matrix.reindex_apply, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv, hk.2, Matrix.submatrix_one_equiv]

end Matrix

/-! Axiom audit: every proof above must use at most
`propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms BitVec.cons_msb_lsbs
#print axioms BitVec.lsbs_zero
#print axioms BitVec.lsbs_cons
#print axioms BitVec.lsbs_xor
#print axioms BitVec.lsbs_or
#print axioms BitVec.lsbs_and
#print axioms BitVec.getElem_eq_msb
#print axioms Complex.one_ne_neg_one
#print axioms Complex.exp_three_pi_div_two
#print axioms Fin.add_neg
#print axioms Matrix.conjTranspose_transpose_comm
#print axioms Matrix.pow_true
#print axioms Matrix.pow_false
#print axioms Matrix.transpose_of_isUnitary
#print axioms Matrix.conjTranspose_of_isUnitary
#print axioms Matrix.mul_of_isUnitary
#print axioms Matrix.smul_of_isUnitary
#print axioms Matrix.kron_of_isUnitary
