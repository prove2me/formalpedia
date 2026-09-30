-- Prove2me | solution 1 for lean_workbook_plus_79225
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:09:27.00612+00:00
-- url     : https://prove2.me/submissions/edf2bf23-d763-4cd7-877f-0e2346bf3c1c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

private theorem inverse_difference_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a+b)⁻¹-a⁻¹*b⁻¹ ≤ (16 : ℝ)⁻¹ := by
  have hs : 0 < a+b := add_pos ha hb
  have hid : (16 : ℝ)⁻¹-((a+b)⁻¹-a⁻¹*b⁻¹) =
      (a+b-8)^2/(16*(a+b)^2)+(a-b)^2/(a*b*(a+b)^2) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hs]
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  positivity

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x+y+3)⁻¹-(x+1)⁻¹*(y+2)⁻¹ ≤ 16⁻¹ := by
  rw [show x+y+3 = (x+1)+(y+2) by ring]
  exact inverse_difference_bound (x+1) (y+2) (by positivity) (by positivity)
