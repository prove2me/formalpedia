-- Prove2me | solution 1 for lean_workbook_plus_30158
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:21:14.305827+00:00
-- url     : https://prove2.me/submissions/c9ab5cad-1047-49c1-8634-3f2089068645

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem cube_outside_unit_disk (z : ℂ) (hz : z ≠ 0)
    (h1 : ‖z + 1‖ ≤ 1) (h2 : ‖z ^ 2 + 1‖ ≤ 1) :
    1 < ‖z ^ 3 + 1‖ := by
  let q := Complex.normSq z
  have hq : 0 < q := Complex.normSq_pos.mpr hz
  have e1 : ‖z + 1‖ ^ 2 = q + 2 * z.re + 1 := by
    simp [q, Complex.sq_norm, Complex.normSq_apply]
    ring
  have e2 : ‖z ^ 2 + 1‖ ^ 2 = q ^ 2 + 4 * z.re ^ 2 - 2 * q + 1 := by
    rw [Complex.sq_norm]
    simp [q, Complex.normSq_apply, pow_succ,
      Complex.mul_re, Complex.mul_im]
    ring
  have e3 : ‖z ^ 3 + 1‖ ^ 2 =
      q ^ 3 + 8 * z.re ^ 3 - 6 * z.re * q + 1 := by
    rw [Complex.sq_norm]
    simp [q, Complex.normSq_apply, pow_succ,
      Complex.mul_re, Complex.mul_im]
    ring
  have hx : z.re < 0 := by nlinarith [norm_nonneg (z + 1)]
  have hgap : 0 ≤ q - 2 * z.re ^ 2 := by
    nlinarith [norm_nonneg (z ^ 2 + 1), sq_nonneg q]
  have hprod := mul_nonpos_of_nonpos_of_nonneg hx.le hgap
  have hcub : z.re ^ 3 < 0 := by
    have := mul_neg_of_neg_of_pos hx (sq_pos_of_ne_zero hx.ne)
    nlinarith
  have hq3 : 0 < q ^ 3 := pow_pos hq 3
  nlinarith [norm_nonneg (z ^ 3 + 1)]

theorem three_unit_disks_iff_zero (z : ℂ) :
    (‖z + 1‖ ≤ 1 ∧ ‖z ^ 2 + 1‖ ≤ 1 ∧ ‖z ^ 3 + 1‖ ≤ 1) ↔ z = 0 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_contra hz
    exact (not_lt_of_ge h3) (cube_outside_unit_disk z hz h1 h2)
  · rintro rfl
    simp

theorem solution (z : ℂ) (hz1 : z ≠ 0) (hz2 : ‖z + 1‖ ≤ 1)
    (hz3 : ‖z ^ 2 + 1‖ ≤ 1) (hz4 : ‖z ^ 3 + 1‖ ≤ 1) : False :=
  hz1 ((three_unit_disks_iff_zero z).mp ⟨hz2, hz3, hz4⟩)

#print axioms cube_outside_unit_disk
#print axioms three_unit_disks_iff_zero
#print axioms solution
