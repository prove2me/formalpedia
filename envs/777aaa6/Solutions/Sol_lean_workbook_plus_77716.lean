-- Prove2me | solution 1 for lean_workbook_plus_77716
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:10:37.653921+00:00
-- url     : https://prove2.me/submissions/f92551e4-121c-4aa9-ba3f-f4654bb782ec

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) (hx : a > 0 ∧ b > 0 ∧ c > 0)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    a / (a + b) + b / (b + c) + c / (c + a) < 2 := by
  obtain ⟨ha, hb, hc⟩ := hx
  have hs : 0 < a + b + c := add_pos (add_pos ha hb) hc
  have h1 : a / (a + b) < (a + c) / (a + b + c) :=
    (div_lt_div_iff₀ (add_pos ha hb) hs).2 (by nlinarith [mul_pos hb hc])
  have h2 : b / (b + c) < (b + a) / (a + b + c) :=
    (div_lt_div_iff₀ (add_pos hb hc) hs).2 (by nlinarith [mul_pos ha hc])
  have h3 : c / (c + a) < (c + b) / (a + b + c) :=
    (div_lt_div_iff₀ (add_pos hc ha) hs).2 (by nlinarith [mul_pos ha hb])
  have hsum : (a + c) / (a + b + c) + (b + a) / (a + b + c) +
      (c + b) / (a + b + c) = 2 := by
    field_simp [ne_of_gt hs]
    ring
  linarith only [h1, h2, h3, hsum]
