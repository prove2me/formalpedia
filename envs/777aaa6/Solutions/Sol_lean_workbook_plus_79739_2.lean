-- Prove2me | solution 2 for lean_workbook_plus_79739
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:10:35.991035+00:00
-- url     : https://prove2.me/submissions/b7094d3b-3236-4752-b77a-227663430681

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (2 + 3 * a) + 1 / (2 + 3 * b) + 1 / (2 + 3 * c)
      ≥ 3 / (2 + a + b + c) := by
  let A : ℝ := 2 + 3 * a
  let B : ℝ := 2 + 3 * b
  let C : ℝ := 2 + 3 * c
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hC : 0 < C := by dsimp [C]; linarith
  have hS : 0 < A + B + C := add_pos (add_pos hA hB) hC
  have hN : 0 ≤ A * (B - C)^2 + B * (C - A)^2 + C * (A - B)^2 :=
    add_nonneg (add_nonneg (mul_nonneg hA.le (sq_nonneg _))
      (mul_nonneg hB.le (sq_nonneg _))) (mul_nonneg hC.le (sq_nonneg _))
  have hD : 0 < A * B * C * (A + B + C) :=
    mul_pos (mul_pos (mul_pos hA hB) hC) hS
  have hid : 1 / A + 1 / B + 1 / C - 9 / (A + B + C) =
      (A * (B - C)^2 + B * (C - A)^2 + C * (A - B)^2) /
        (A * B * C * (A + B + C)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC, ne_of_gt hS]
    ring
  have hbound : 9 / (A + B + C) ≤ 1 / A + 1 / B + 1 / C := by
    have hn := div_nonneg hN hD.le
    linarith only [hid, hn]
  have hs : 0 < 2 + a + b + c := by linarith
  have hquot : 9 / (A + B + C) = 3 / (2 + a + b + c) := by
    apply (div_eq_div_iff (ne_of_gt hS) (ne_of_gt hs)).2
    dsimp [A, B, C]
    ring
  rw [hquot] at hbound
  exact hbound
