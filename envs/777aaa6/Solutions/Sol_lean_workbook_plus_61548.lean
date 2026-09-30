-- Prove2me | solution 1 for lean_workbook_plus_61548
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:59:31.277142+00:00
-- url     : https://prove2.me/submissions/55bb7562-7744-4f5c-9763-03523e2c55af

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 ≥ a * b * c * (a + b + c) ↔ (a * b - b * c) ^ 2 + (a * c - b * c) ^ 2 + (a * b - a * c) ^ 2 ≥ 0 := by
  have hL : a ^ 4 + b ^ 4 + c ^ 4 ≥ a * b * c * (a + b + c) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - c ^ 2),
      sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c), sq_nonneg (a * b - a * c)]
  have hR : (a * b - b * c) ^ 2 + (a * c - b * c) ^ 2 + (a * b - a * c) ^ 2 ≥ 0 := by positivity
  exact ⟨fun _ => hR, fun _ => hL⟩
