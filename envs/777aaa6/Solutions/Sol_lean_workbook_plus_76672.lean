-- Prove2me | solution 1 for lean_workbook_plus_76672
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:46:53.916876+00:00
-- url     : https://prove2.me/submissions/e7c5c5a0-dfaa-4dcb-a045-4cd94125ef66

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) ≥ 9 / (a + b + c) := by
  have hab := add_pos ha hb
  have hbc := add_pos hb hc
  have hca := add_pos hc ha
  have hp := add_pos hab hc
  have hid : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c) =
      ((a - b)^2 * (a + b) + (b - c)^2 * (b + c) + (c - a)^2 * (c + a)) /
        ((a + b + c) * (a + b) * (b + c) * (c + a)) := by
    field_simp [ne_of_gt hab, ne_of_gt hbc, ne_of_gt hca, ne_of_gt hp]
    ring
  have hnum : 0 ≤ (a - b)^2 * (a + b) +
      (b - c)^2 * (b + c) + (c - a)^2 * (c + a) :=
    add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) hab.le)
      (mul_nonneg (sq_nonneg _) hbc.le)) (mul_nonneg (sq_nonneg _) hca.le)
  have hd : 0 < (a + b + c) * (a + b) * (b + c) * (c + a) :=
    mul_pos (mul_pos (mul_pos hp hab) hbc) hca
  have hq := div_nonneg hnum hd.le
  linarith
