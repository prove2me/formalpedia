-- Prove2me | solution 1 for lean_workbook_plus_2847
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:39:47.819158+00:00
-- url     : https://prove2.me/submissions/02122577-adb2-4587-ad25-8a6f1c81cf36

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) = 16) : a * b ≤ 1   := by
  by_contra hbad
  have habgt : (1 : ℝ) < a * b := lt_of_not_ge hbad
  have hsumpos : (0 : ℝ) < a + b := add_pos ha hb
  have hsum : (2 : ℝ) < a + b := by
    by_contra! hsmall
    have hprod : (0 : ℝ) ≤ (2 - (a + b)) * (2 + (a + b)) :=
      mul_nonneg (sub_nonneg.mpr hsmall) (by linarith only [hsumpos])
    nlinarith only [hprod, sq_nonneg (a - b), habgt]
  let q : ℝ := a + b - 2
  let r : ℝ := a * b - 1
  have hq : (0 : ℝ) < q := sub_pos.mpr hsum
  have hr : (0 : ℝ) < r := sub_pos.mpr habgt
  have hda : (0 : ℝ) < a + 1 := by linarith only [ha]
  have hdb : (0 : ℝ) < b + 1 := by linarith only [hb]
  have hidentity :
      ((a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) - 16) *
          ((a + 1) * (b + 1)) =
        2 * q ^ 3 + 2 * (q ^ 2 * r) + 18 * q ^ 2 + 9 * (q * r) +
          39 * q + r ^ 2 + r := by
    dsimp [q, r]
    field_simp [ne_of_gt hda, ne_of_gt hdb] <;> ring
  have hzero :
      2 * q ^ 3 + 2 * (q ^ 2 * r) + 18 * q ^ 2 + 9 * (q * r) +
        39 * q + r ^ 2 + r = 0 := by
    rw [hab, sub_self, zero_mul] at hidentity
    exact hidentity.symm
  have hq3 : (0 : ℝ) ≤ q ^ 3 := pow_nonneg hq.le 3
  have hq2r : (0 : ℝ) ≤ q ^ 2 * r := mul_nonneg (sq_nonneg q) hr.le
  have hqr : (0 : ℝ) ≤ q * r := mul_nonneg hq.le hr.le
  have hpositive : (0 : ℝ) <
      2 * q ^ 3 + 2 * (q ^ 2 * r) + 18 * q ^ 2 + 9 * (q * r) +
        39 * q + r ^ 2 + r := by
    linarith only [hq3, hq2r, sq_nonneg q, hqr, hq, sq_nonneg r, hr]
  exact (ne_of_gt hpositive) hzero

#print axioms solution
