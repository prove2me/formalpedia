-- Prove2me | solution 1 for lean_workbook_plus_56030
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:48.257354+00:00
-- url     : https://prove2.me/submissions/aa573a8a-4bac-4e2b-a17b-df81a6fcc2dc

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : ∃ (f : ℕ → ℕ), f 0 = 2 ∧ ∀ k, f (k + 1) = f 1 * f k - f (k - 1) := by
  refine ⟨fun _ => 2, rfl, fun k => ?_⟩
  norm_num
