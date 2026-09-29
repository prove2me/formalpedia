-- Prove2me | solution 1 for QuantumEML.one_lt_scalarLogNormSq_five_fourths
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:19:39.801922+00:00
-- url     : https://prove2.me/submissions/e926d823-6573-4e26-8d48-b157e9b0e093

-- Sol generated from NumberTheory/EMLQuantumScalarLogSharp.lean
import Mathlib
import Definitions.Def_NumberTheory_EMLQuantumScalarLogSharp
import Theorems.Thm_QuantumEML_self_div_le_arctan

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




/-- Exact addition identity `arctan (5/4) = π/4 + arctan (1/9)`. -/
theorem arctan_five_fourths_eq : Real.arctan (5 / 4) = π / 4 + Real.arctan (1 / 9) := by
  have h := Real.arctan_add (x := 1) (y := 1 / 9) (by norm_num)
  rw [Real.arctan_one] at h
  rw [h]; norm_num

/-! ### The scalar logarithmic norm and its closed form -/









/-! ### Strict monotonicity and uniqueness -/





/-! ### The tightened certified interval `[6/5, 5/4]` -/









/-! ### The radius map is a bijection of `[0, ∞)` -/




/-! ### Lifting the scalar factor to matrix C⋆-algebras -/


/-! ### The polar-normalized logarithmic factor -/





open QuantumEML in
theorem solution: 1 < scalarLogNormSq (5 / 4) := by
  have hL : (0.9126593 : ℝ) ≤ Real.log (1 + (5 / 4 : ℝ) ^ 2) := by
    have h : 1 + (5 / 4 : ℝ) ^ 2 = 2 * (41 / 32) := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num)]
    have h1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h2 : 1 - (41 / 32 : ℝ)⁻¹ ≤ Real.log (41 / 32) := Real.one_sub_inv_le_log_of_pos (by norm_num)
    norm_num at h2 ⊢
    linarith
  have hA : (0.8951 : ℝ) ≤ Real.arctan (5 / 4) := by
    rw [arctan_five_fourths_eq]
    have h := self_div_le_arctan (y := (1 / 9 : ℝ)) (by norm_num)
    norm_num at h
    have hpi : (3.141592 : ℝ) < π := Real.pi_gt_d6
    linarith
  unfold scalarLogNormSq
  nlinarith
