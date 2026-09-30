-- Prove2me | solution 1 for lean_workbook_plus_79051
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:35:10.114059+00:00
-- url     : https://prove2.me/submissions/f086a485-7a48-464f-9e4c-68bc258c0494

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (hab : 0 < a) (hbc : 0 < b) (hca : 0 < c)
    (habc : 0 < a * b * c) (h : a * b + b * c + c * a + a * b * c ≥ 4) :
    a + b + c ≥ 3 + (b - c) ^ 2 / (b + c + 4) := by
  let u := b + c
  let v := b * c
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hbase : 0 ≤ a * (u + v) + v - 4 := by dsimp [u, v]; nlinarith
  have hid : (a * (u + 4) - (12 - u - 4 * v)) * (u + v) =
      (u + 4) * (a * (u + v) + v - 4) + (u + 2 * v - 4) ^ 2 := by ring
  have hprod : 0 ≤ (a * (u + 4) - (12 - u - 4 * v)) * (u + v) := by
    rw [hid]
    exact add_nonneg (mul_nonneg (by positivity) hbase) (sq_nonneg _)
  have hlin : 0 ≤ a * (u + 4) - (12 - u - 4 * v) :=
    nonneg_of_mul_nonneg_left hprod (add_pos hu hv)
  have hden : 0 < b + c + 4 := by positivity
  have hdiv : (b - c) ^ 2 / (b + c + 4) ≤ a + b + c - 3 := by
    apply (div_le_iff₀ hden).mpr
    dsimp [u, v] at hlin
    nlinarith
  linarith

#print axioms solution
