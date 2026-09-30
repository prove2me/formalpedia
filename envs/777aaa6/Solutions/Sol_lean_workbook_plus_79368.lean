-- Prove2me | solution 1 for lean_workbook_plus_79368
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:10:36.823016+00:00
-- url     : https://prove2.me/submissions/9a7ec5df-27f3-4abe-a10d-27bcda8d110b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private theorem pair_bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    4 / (x + y) ≤ 1 / x + 1 / y := by
  have hs := add_pos hx hy
  have hid : 1 / x + 1 / y - 4 / (x + y) = (x - y)^2 / (x * y * (x + y)) := by
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hs]
    ring
  have hn := div_nonneg (sq_nonneg (x - y)) (mul_pos (mul_pos hx hy) hs).le
  linarith only [hid, hn]

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (1 / a + 1 / b + 1 / c) ≥ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
  have h1 := pair_bound a b ha hb
  have h2 := pair_bound b c hb hc
  have h3 := pair_bound c a hc ha
  simp only [div_eq_mul_inv, one_mul] at h1 h2 h3 ⊢
  linarith only [h1, h2, h3]
