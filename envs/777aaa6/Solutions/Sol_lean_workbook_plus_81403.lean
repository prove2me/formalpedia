-- Prove2me | solution 1 for lean_workbook_plus_81403
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:13:48.490857+00:00
-- url     : https://prove2.me/submissions/53e97453-823b-47da-b296-3e70729c0928

import Mathlib

theorem solution (a b c l_a l_b l_c : ℝ)
    (h₁ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₂ : a + b > c) (h₃ : a + c > b) (h₄ : b + c > a)
    (h₅ : l_a = 2 * b * c / (b + c))
    (h₆ : l_b = 2 * c * a / (c + a))
    (h₇ : l_c = 2 * a * b / (a + b)) :
    (a + b + c) ^ 2 > l_a * (b + c) + l_b * (c + a) + l_c * (a + b) ∧
    l_a * (b + c) + l_b * (c + a) + l_c * (a + b) > (a + b + c) ^ 2 / 2 := by
  rcases h₁ with ⟨ha, hb, hc⟩
  rw [h₅, h₆, h₇, div_mul_cancel₀ _ (ne_of_gt (add_pos hb hc)),
    div_mul_cancel₀ _ (ne_of_gt (add_pos hc ha)),
    div_mul_cancel₀ _ (ne_of_gt (add_pos ha hb))]
  constructor
  · nlinarith [sq_pos_of_pos ha, sq_nonneg b, sq_nonneg c]
  · have hp := mul_pos (show 0 < a + b - c by linarith) hc
    have hq := mul_pos (show 0 < a + c - b by linarith) hb
    have hr := mul_pos (show 0 < b + c - a by linarith) ha
    nlinarith
