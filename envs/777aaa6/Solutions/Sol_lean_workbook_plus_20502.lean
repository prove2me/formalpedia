-- Prove2me | solution 1 for lean_workbook_plus_20502
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:50:39.064379+00:00
-- url     : https://prove2.me/submissions/402361df-8cc2-4459-91da-01757d165334

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x * y ≥ 1) : 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 1 / 8 * (x * y) ≥ 7 / 8   := by
  let t : ℝ := x * y
  let s : ℝ := x ^ 2 + y ^ 2
  have ht : 1 ≤ t := h
  have hs : 2 * t ≤ s := by dsimp [s, t]; nlinarith [sq_nonneg (x - y)]
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hy : 0 < 1 + y ^ 2 := by positivity
  have hd : 0 < 1 + t := by linarith
  have hid : 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) - 2 / (1 + t) =
      (t - 1) * (s - 2 * t) / ((1 + x ^ 2) * (1 + y ^ 2) * (1 + t)) := by
    dsimp [s, t]
    field_simp
    <;> ring
  have hn : 0 ≤ (t - 1) * (s - 2 * t) / ((1 + x ^ 2) * (1 + y ^ 2) * (1 + t)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have hid2 : 2 / (1 + t) + t / 8 - 7 / 8 = (t - 3) ^ 2 / (8 * (1 + t)) := by
    field_simp
    <;> ring
  have hn2 : 0 ≤ (t - 3) ^ 2 / (8 * (1 + t)) := div_nonneg (sq_nonneg _) (by positivity)
  change 7 / 8 ≤ 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 1 / 8 * t
  linarith only [hid, hn, hid2, hn2]
