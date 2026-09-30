-- Prove2me | solution 1 for lean_workbook_plus_11835
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:09:22.943581+00:00
-- url     : https://prove2.me/submissions/f8dabde6-c780-48f0-9533-a2c26c609b80

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1) = 2 → a * b * c ≤ 1 / 8) := by
  intro h
  have ha1 : (0:ℝ) < a + 1 := by linarith
  have hb1 : (0:ℝ) < b + 1 := by linarith
  have hc1 : (0:ℝ) < c + 1 := by linarith
  -- clear denominators: 2abc + ab + bc + ca = 1
  have key : 2 * (a * b * c) + (a * b + b * c + c * a) = 1 := by
    field_simp at h
    nlinarith [h]
  -- AM-GM for x = ab, y = bc, z = ca : (x+y+z)^3 ≥ 27 xyz
  set x := a * b with hx
  set y := b * c with hy
  set z := c * a with hz
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hz0 : 0 ≤ z := by positivity
  have amgm : 27 * (x * y * z) ≤ (x + y + z) ^ 3 := by
    nlinarith [mul_nonneg (add_nonneg (add_nonneg hx0 hy0) hz0)
        (add_nonneg (add_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z))) (sq_nonneg (x - z))),
      mul_nonneg hx0 (sq_nonneg (y - z)), mul_nonneg hy0 (sq_nonneg (x - z)),
      mul_nonneg hz0 (sq_nonneg (x - y))]
  have hxyz : x * y * z = (a * b * c) ^ 2 := by rw [hx, hy, hz]; ring
  set p := a * b * c with hp
  have hp0 : 0 < p := by positivity
  have hq : x + y + z = 1 - 2 * p := by linarith
  rw [hxyz, hq] at amgm
  -- (1-2p)^3 ≥ 27 p^2  ⟺  (8p-1)(p+1)^2 ≤ 0
  nlinarith [amgm, sq_nonneg (p + 1), mul_pos hp0 hp0, mul_nonneg hp0.le (sq_nonneg (p + 1))]
