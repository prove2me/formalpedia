-- Prove2me | solution 1 for lean_workbook_plus_75442
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:34:15.801714+00:00
-- url     : https://prove2.me/submissions/4927607a-d198-4581-9daf-cdecb39625ab

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem pair_bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (3 * x - y) / 4 ≤ x ^ 2 / (x + y) := by
  have hxy : 0 < x + y := add_pos hx hy
  have hid : x ^ 2 / (x + y) - (3 * x - y) / 4 =
      (x - y) ^ 2 / (4 * (x + y)) := by
    field_simp
    <;> ring
  have hs := div_nonneg (sq_nonneg (x - y)) (mul_pos (by norm_num : (0 : ℝ) < 4) hxy).le
  linarith

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a) ≥
      (a + b + c) / 2 := by
  have hab := pair_bound a b ha hb
  have hbc := pair_bound b c hb hc
  have hca := pair_bound c a hc ha
  linarith

#print axioms solution
