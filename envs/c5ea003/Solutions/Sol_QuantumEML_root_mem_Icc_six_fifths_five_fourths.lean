-- Prove2me | solution 1 for QuantumEML.root_mem_Icc_six_fifths_five_fourths
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:46:27.13436+00:00
-- url     : https://prove2.me/submissions/109b94af-da3f-463f-b352-046613094d1f

-- Sol generated from NumberTheory/EMLQuantumScalarLogSharp.lean
import Mathlib
import Definitions.Def_NumberTheory_EMLQuantumScalarLogSharp
import Theorems.Thm_QuantumEML_one_lt_scalarLogNormSq_five_fourths
import Theorems.Thm_QuantumEML_scalarLogNormSq_six_fifths_lt_one

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

theorem scalarLogNormSq_nonneg (t : ℝ) : 0 ≤ scalarLogNormSq t := by
  rw [← scalarLogNorm_sq]; positivity

theorem scalarLogNorm_eq_sqrt (t : ℝ) : scalarLogNorm t = Real.sqrt (scalarLogNormSq t) := by
  rw [← scalarLogNorm_sq, Real.sqrt_sq (scalarLogNorm_nonneg t)]

/-! ### Strict monotonicity and uniqueness -/

theorem log_one_add_sq_nonneg (t : ℝ) : 0 ≤ Real.log (1 + t ^ 2) :=
  Real.log_nonneg (by nlinarith [sq_nonneg t])

/-- The square of the scalar logarithmic norm is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_scalarLogNormSq : StrictMonoOn scalarLogNormSq (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  simp only [mem_Ici] at ha hb
  have h1 : Real.log (1 + a ^ 2) < Real.log (1 + b ^ 2) := by
    apply Real.log_lt_log (by positivity)
    nlinarith
  have h2 : Real.arctan a < Real.arctan b := Real.arctan_strictMono hab
  have ha1 := log_one_add_sq_nonneg a
  have ha2 : 0 ≤ Real.arctan a := Real.arctan_nonneg.2 ha
  unfold scalarLogNormSq
  nlinarith

/-- **Strict monotonicity.**  `t ↦ ‖log (1 + t i)‖` is strictly increasing on
`[0, ∞)`. -/
theorem strictMonoOn_scalarLogNorm : StrictMonoOn scalarLogNorm (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  have h := strictMonoOn_scalarLogNormSq ha hb hab
  rw [scalarLogNorm_eq_sqrt, scalarLogNorm_eq_sqrt]
  exact Real.sqrt_lt_sqrt (scalarLogNormSq_nonneg a) h


/-! ### The tightened certified interval `[6/5, 5/4]` -/



/-- At `t = 6/5` the logarithm is still strictly inside the unit circle. -/
theorem scalarLogNorm_six_fifths_lt_one : scalarLogNorm (6 / 5) < 1 := by
  have h := scalarLogNormSq_six_fifths_lt_one
  nlinarith [scalarLogNorm_sq (6 / 5), scalarLogNorm_nonneg (6 / 5)]

/-- At `t = 5/4` the logarithm is already strictly outside the unit circle. -/
theorem one_lt_scalarLogNorm_five_fourths : 1 < scalarLogNorm (5 / 4) := by
  have h := one_lt_scalarLogNormSq_five_fourths
  nlinarith [scalarLogNorm_sq (5 / 4), scalarLogNorm_nonneg (5 / 4)]





/-! ### The radius map is a bijection of `[0, ∞)` -/




/-! ### Lifting the scalar factor to matrix C⋆-algebras -/


/-! ### The polar-normalized logarithmic factor -/





open QuantumEML in
theorem solution{t : ℝ} (ht : 0 < t) (h : scalarLogNorm t = 1) :
    t ∈ Icc (6 / 5 : ℝ) (5 / 4) := by
  constructor
  · by_contra hlt
    push_neg at hlt
    have := strictMonoOn_scalarLogNorm (mem_Ici.2 ht.le) (mem_Ici.2 (by norm_num)) hlt
    rw [h] at this
    exact absurd this (not_lt.2 scalarLogNorm_six_fifths_lt_one.le)
  · by_contra hgt
    push_neg at hgt
    have := strictMonoOn_scalarLogNorm (mem_Ici.2 (by norm_num : (0:ℝ) ≤ 5 / 4))
      (mem_Ici.2 ht.le) hgt
    rw [h] at this
    exact absurd this (not_lt.2 one_lt_scalarLogNorm_five_fourths.le)
