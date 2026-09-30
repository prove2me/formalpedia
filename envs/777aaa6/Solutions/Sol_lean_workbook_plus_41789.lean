-- Prove2me | solution 1 for lean_workbook_plus_41789
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:01:17.230908+00:00
-- url     : https://prove2.me/submissions/8c44a846-97f4-46e9-a8b8-431ab8ab183c

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℤ) : n ^ 2 * (n - 1) * (3 * n + 1) ≥ 0 := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hp : 0 ≤ (n - 1) * (3 * n + 1) :=
      mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    simpa only [mul_assoc] using mul_nonneg (sq_nonneg n) hp
  · simp [hn]
  · exact mul_nonneg (mul_nonneg (sq_nonneg n) (by omega)) (by omega)

#print axioms solution
