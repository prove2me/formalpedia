-- Prove2me | solution 1 for lean_workbook_plus_17079
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:27.306418+00:00
-- url     : https://prove2.me/submissions/7fd0683a-1a56-44c7-a85a-d91a80b7871a

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ A B : ℝ, ∀ n : ℕ, (A * 2 ^ n + B * 3 ^ n) = (5 * (A * 2 ^ (n - 1) + B * 3 ^ (n - 1)) - 6 * (A * 2 ^ (n - 2) + B * 3 ^ (n - 2))) := by
  refine ⟨0, 0, fun n => ?_⟩
  simp
