-- Prove2me | solution 1 for lean_workbook_plus_53578
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:35:08.186763+00:00
-- url     : https://prove2.me/submissions/e07460f2-02d1-48ac-87bb-46e9cf5df4e0

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x : ℝ, x ∈ Set.Icc 0 1 → x^5 + x - x^8 - x^2 ≤ 1 := by
  intro x ⟨h0, h1⟩
  have h2 : x ^ 5 ≤ x ^ 2 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have h3 : 0 ≤ x ^ 8 := by positivity
  linarith
