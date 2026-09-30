-- Prove2me | solution 1 for lean_workbook_plus_55302
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:03:43.404563+00:00
-- url     : https://prove2.me/submissions/a648c183-f42f-48b9-983b-8ce30d4c1614

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem asymmetric_power_remainder (x y : ℝ) :
    2 - x ^ 3 - y ^ 3 = 3 * (x ^ 2 + y ^ 3 - x ^ 3 - y ^ 4) +
      (x - 1) ^ 2 * (2 * x + 1) + (y - 1) ^ 2 * (3 * y ^ 2 + 2 * y + 1) := by
  ring

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 + y ^ 3 ≥ x ^ 3 + y ^ 4) : x ^ 3 + y ^ 3 ≤ 2 := by
  have h1 := mul_nonneg (sq_nonneg (x - 1)) (show 0 ≤ 2 * x + 1 by linarith)
  have h2 := mul_nonneg (sq_nonneg (y - 1))
    (show 0 ≤ 3 * y ^ 2 + 2 * y + 1 by nlinarith [sq_nonneg y])
  linarith [asymmetric_power_remainder x y]

theorem asymmetric_power_equality (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 + y ^ 3 ≥ x ^ 3 + y ^ 4) :
    x ^ 3 + y ^ 3 = 2 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro he
    have hp : 0 < 2 * x + 1 := by linarith
    have hq : 0 < 3 * y ^ 2 + 2 * y + 1 := by nlinarith [sq_nonneg y]
    have h1 := mul_nonneg (sq_nonneg (x - 1)) hp.le
    have h2 := mul_nonneg (sq_nonneg (y - 1)) hq.le
    have hz1 : (x - 1) ^ 2 * (2 * x + 1) = 0 := by
      linarith [asymmetric_power_remainder x y]
    have hz2 : (y - 1) ^ 2 * (3 * y ^ 2 + 2 * y + 1) = 0 := by
      linarith [asymmetric_power_remainder x y]
    have hxx := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz1).resolve_right hp.ne')
    have hyy := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz2).resolve_right hq.ne')
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ring

#print axioms solution
#print axioms asymmetric_power_equality
