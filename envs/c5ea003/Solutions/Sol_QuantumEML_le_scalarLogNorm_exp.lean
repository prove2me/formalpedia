-- Prove2me | solution 1 for QuantumEML.le_scalarLogNorm_exp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:46:26.227278+00:00
-- url     : https://prove2.me/submissions/24db4038-1ef3-4e5e-8247-02916a502e85

-- Sol generated from NumberTheory/EMLQuantumScalarLogSharp.lean
import Mathlib
import Definitions.Def_NumberTheory_EMLQuantumScalarLogSharp

/-!
# Sharpening the scalar unitary logarithmic factor

This file continues the study of the *scalar-log unit-circle* problem for
quantum EML activations begun in `Catalog/NumberTheory/EMLQuantumScalarLog.lean`,
where the existence of a parameter `t ≠ 0` with `‖log (1 + t i)‖ = 1` was
established with the crude certified interval `[1/2, 3]`.  (The catalog files
are compiled independently of one another, so the two basic definitions
`scalarLogNorm` and the auxiliary lemmas are restated here verbatim; everything
past that point is new.)

The results proved here answer the first three of the "future directions"
attached to that file, and add a fourth.

## Main results

* `QuantumEML.scalarLogNorm_sq` : the closed form
  `‖log (1 + t i)‖ ^ 2 = (log (1 + t ^ 2) / 2) ^ 2 + arctan t ^ 2`.
* `QuantumEML.strictMonoOn_scalarLogNorm` : `t ↦ ‖log (1 + t i)‖` is *strictly
  increasing* on `[0, ∞)`.  This upgrades the previous existence statement to a
  uniqueness statement.
* `QuantumEML.existsUnique_pos_scalarLogNorm_eq_one` : there is exactly one
  positive solution of `‖log (1 + t i)‖ = 1`.
* `QuantumEML.scalarLogNorm_six_fifths_lt_one`,
  `QuantumEML.one_lt_scalarLogNorm_five_fourths`,
  `QuantumEML.root_mem_Icc_six_fifths_five_fourths` : the certified interval is
  tightened from `[1/2, 3]` to `[6/5, 5/4]`, a factor `30` improvement in
  width.  The proof uses the exact `arctan` addition identities
  `arctan (6/5) = π/4 + arctan (1/11)` and `arctan (5/4) = π/4 + arctan (1/9)`
  together with the elementary two-sided bound
  `y / (1 + y ^ 2) ≤ arctan y ≤ y` and the rational bounds
  `1 - x⁻¹ ≤ log x ≤ x - 1` applied after splitting off `log 2`.
* `smul_one_mem_unitary` : a scalar of modulus one times the identity of any
  complex star algebra is unitary; hence the scalar logarithmic factor lifts to
  matrix C⋆-algebras (`QuantumEML.exists_scalar_log_smul_one_mem_unitary`).
* `QuantumEML.polarUnit_smul_one_mem_unitary` : the *polar-normalized*
  logarithmic factor `log (1 + t i) / ‖log (1 + t i)‖` is unitary for **every**
  `t ≠ 0`, not merely for the certified root.
-/

noncomputable section

open Complex Real Set

/-! ### A scalar of modulus one is a unitary in any complex star algebra -/




/-! ### Elementary two-sided bounds for `arctan` -/

open QuantumEML





/-! ### The scalar logarithmic norm and its closed form -/



theorem arg_one_add_mul_I (t : ℝ) : (1 + (t : ℂ) * I).arg = Real.arctan t := by
  rw [Complex.arg, if_pos (by simp), Real.arctan_eq_arcsin]
  congr 1
  rw [Complex.norm_def]
  simp [Complex.normSq]
  ring_nf

theorem norm_one_add_mul_I (t : ℝ) : ‖1 + (t : ℂ) * I‖ = Real.sqrt (1 + t ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq]
  ring

/-- **Closed form.** `‖log (1 + t i)‖ ^ 2 = (log (1 + t ^ 2) / 2) ^ 2 + arctan t ^ 2`. -/
theorem scalarLogNorm_sq (t : ℝ) : scalarLogNorm t ^ 2 = scalarLogNormSq t := by
  have hre : (Complex.log (1 + (t : ℂ) * I)).re = Real.log (1 + t ^ 2) / 2 := by
    rw [Complex.log_re, norm_one_add_mul_I, Real.log_sqrt (by positivity)]
  have him : (Complex.log (1 + (t : ℂ) * I)).im = Real.arctan t := by
    rw [Complex.log_im, arg_one_add_mul_I]
  rw [scalarLogNorm, scalarLogNormSq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
  ring

theorem scalarLogNorm_nonneg (t : ℝ) : 0 ≤ scalarLogNorm t := norm_nonneg _


theorem scalarLogNorm_eq_sqrt (t : ℝ) : scalarLogNorm t = Real.sqrt (scalarLogNormSq t) := by
  rw [← scalarLogNorm_sq, Real.sqrt_sq (scalarLogNorm_nonneg t)]

/-! ### Strict monotonicity and uniqueness -/

theorem log_one_add_sq_nonneg (t : ℝ) : 0 ≤ Real.log (1 + t ^ 2) :=
  Real.log_nonneg (by nlinarith [sq_nonneg t])




/-! ### The tightened certified interval `[6/5, 5/4]` -/









/-! ### The radius map is a bijection of `[0, ∞)` -/




/-! ### Lifting the scalar factor to matrix C⋆-algebras -/


/-! ### The polar-normalized logarithmic factor -/





open QuantumEML in
theorem solution(r : ℝ) : r ≤ scalarLogNorm (Real.exp r) := by
  have hlog : r ≤ Real.log (1 + Real.exp r ^ 2) / 2 := by
    have h1 : Real.exp r ^ 2 = Real.exp (2 * r) := by rw [← Real.exp_nat_mul]; ring_nf
    have h2 : Real.exp (2 * r) ≤ 1 + Real.exp r ^ 2 := by rw [h1]; linarith
    have h3 := Real.log_le_log (Real.exp_pos (2 * r)) h2
    rw [Real.log_exp] at h3
    linarith
  have hL0 : 0 ≤ Real.log (1 + Real.exp r ^ 2) := log_one_add_sq_nonneg _
  have hsq : (Real.log (1 + Real.exp r ^ 2) / 2) ^ 2 ≤ scalarLogNormSq (Real.exp r) := by
    unfold scalarLogNormSq; nlinarith [sq_nonneg (Real.arctan (Real.exp r))]
  rw [scalarLogNorm_eq_sqrt]
  calc r ≤ Real.log (1 + Real.exp r ^ 2) / 2 := hlog
    _ = Real.sqrt ((Real.log (1 + Real.exp r ^ 2) / 2) ^ 2) := by
        rw [Real.sqrt_sq (by linarith)]
    _ ≤ Real.sqrt (scalarLogNormSq (Real.exp r)) := Real.sqrt_le_sqrt hsq
