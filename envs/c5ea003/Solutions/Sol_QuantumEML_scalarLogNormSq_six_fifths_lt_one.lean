-- Prove2me | solution 1 for QuantumEML.scalarLogNormSq_six_fifths_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:19:40.421969+00:00
-- url     : https://prove2.me/submissions/061e0c86-ed5f-4d84-8156-088802b69d53

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

/-- `arctan y ≤ y` for `y ≥ 0`, from the tangent inequality `x ≤ tan x`. -/
theorem arctan_le_self {y : ℝ} (hy : 0 ≤ y) : Real.arctan y ≤ y := by
  have h := Real.le_tan (Real.arctan_nonneg.2 hy) (Real.arctan_lt_pi_div_two y)
  rwa [Real.tan_arctan] at h


/-- Exact addition identity `arctan (6/5) = π/4 + arctan (1/11)`. -/
theorem arctan_six_fifths_eq : Real.arctan (6 / 5) = π / 4 + Real.arctan (1 / 11) := by
  have h := Real.arctan_add (x := 1) (y := 1 / 11) (by norm_num)
  rw [Real.arctan_one] at h
  rw [h]; norm_num


/-! ### The scalar logarithmic norm and its closed form -/









/-! ### Strict monotonicity and uniqueness -/





/-! ### The tightened certified interval `[6/5, 5/4]` -/









/-! ### The radius map is a bijection of `[0, ∞)` -/




/-! ### Lifting the scalar factor to matrix C⋆-algebras -/


/-! ### The polar-normalized logarithmic factor -/





open QuantumEML in
theorem solution: scalarLogNormSq (6 / 5) < 1 := by
  have hL : Real.log (1 + (6 / 5 : ℝ) ^ 2) ≤ 0.9131472 := by
    have h : 1 + (6 / 5 : ℝ) ^ 2 = 2 * (61 / 50) := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num)]
    have h1 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have h2 : Real.log (61 / 50) ≤ 61 / 50 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hL0 : 0 ≤ Real.log (1 + (6 / 5 : ℝ) ^ 2) := Real.log_nonneg (by norm_num)
  have hA : Real.arctan (6 / 5) ≤ 0.8785 := by
    rw [arctan_six_fifths_eq]
    have := arctan_le_self (y := (1 / 11 : ℝ)) (by norm_num)
    have hpi : π < 3.15 := Real.pi_lt_d2
    linarith
  have hA0 : 0 ≤ Real.arctan (6 / 5) := Real.arctan_nonneg.2 (by norm_num)
  unfold scalarLogNormSq
  nlinarith
