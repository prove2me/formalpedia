-- Prove2me | solution 1 for lean_workbook_plus_6407
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:09.492282+00:00
-- url     : https://prove2.me/submissions/c1e73864-2da8-4dff-8d11-8e4c6ed6af72

import Mathlib.Analysis.Complex.Basic

theorem solution (b a : ℝ) (ha : a ≠ 0) : |1 + b / a| + 2 * |1 - b / a| ≥ 2 := by
  rcases abs_cases (1 + b / a) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
  rcases abs_cases (1 - b / a) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
  linarith
