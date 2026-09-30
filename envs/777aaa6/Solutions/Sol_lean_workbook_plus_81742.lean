-- Prove2me | solution 1 for lean_workbook_plus_81742
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:50.47488+00:00
-- url     : https://prove2.me/submissions/c5ac248c-eb79-427f-a403-8255274e5a0a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a : ℝ) : (1 + a^2 + a^4)^4 ≥ 9 * a^4 * (a + a^2 + a^3)^2 := by
  let S := 1 + a^2 + a^4
  let A := a + a^2 + a^3
  have ht : 0 ≤ a^2 + a + 1 := by nlinarith [sq_nonneg (a + 1 / 2)]
  have hS : 3 * a^2 ≤ S := by dsimp [S]; nlinarith [sq_nonneg (a^2 - 1)]
  have hm : 0 ≤ S - A := by
    have heq : S - A = (a - 1)^2 * (a^2 + a + 1) := by dsimp [S, A]; ring
    rw [heq]
    exact mul_nonneg (sq_nonneg _) ht
  have hp : 0 ≤ S + A := by
    have heq : S + A = (a^2 + 1) * (a^2 + a + 1) := by dsimp [S, A]; ring
    rw [heq]
    exact mul_nonneg (by positivity) ht
  have hAsq : A^2 ≤ S^2 := by nlinarith [mul_nonneg hm hp]
  have hSsq : 9 * a^4 ≤ S^2 := by
    have hs0 : 0 ≤ S := by dsimp [S]; positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (show 0 ≤ S + 3 * a^2 by positivity)]
  have hprod := mul_le_mul hSsq hAsq (sq_nonneg A) (sq_nonneg S)
  change 9 * a^4 * (a + a^2 + a^3)^2 ≤ (1 + a^2 + a^4)^4
  calc
    9 * a^4 * (a + a^2 + a^3)^2 ≤ S^2 * S^2 := hprod
    _ = (1 + a^2 + a^4)^4 := by dsimp [S]; ring
