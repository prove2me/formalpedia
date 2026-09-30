-- Prove2me | solution 1 for lean_workbook_plus_38575
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:41:46.22697+00:00
-- url     : https://prove2.me/submissions/39de698c-9703-4960-8aa6-347b9b0607ab

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c : ℝ} (h1 : a ≥ b ∧ b ≥ c) (h2 : 0 < a ∧ 0 < b ∧ 0 < c) (h3 : b + c > a) : a^2 * b^2 + b^2 * c^2 + a^2 * c^2 ≥ (a + b + c) * (a + b - c) * (a - b + c) * (b + c - a) := by
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (a^2 - c^2)]
