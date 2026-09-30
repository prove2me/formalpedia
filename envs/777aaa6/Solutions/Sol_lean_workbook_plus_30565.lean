-- Prove2me | solution 1 for lean_workbook_plus_30565
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:59:25.802165+00:00
-- url     : https://prove2.me/submissions/aeee545c-39e9-4c2f-a484-2087b45bf16f

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a * b / (2 * c + a + b) ≤ a * b / 4 * (1 / (c + a) + 1 / (c + b)) := by
  intro a b c ⟨ha, hb, hc⟩
  have h1 : 0 < c + a := by linarith
  have h2 : 0 < c + b := by linarith
  have h3 : 0 < 2 * c + a + b := by linarith
  have key : a * b / 4 * (1 / (c + a) + 1 / (c + b)) - a * b / (2 * c + a + b)
      = a * b * (a - b) ^ 2 / (4 * (c + a) * (c + b) * (2 * c + a + b)) := by
    field_simp
    ring
  have hnn : 0 ≤ a * b * (a - b) ^ 2 / (4 * (c + a) * (c + b) * (2 * c + a + b)) := by
    positivity
  linarith
