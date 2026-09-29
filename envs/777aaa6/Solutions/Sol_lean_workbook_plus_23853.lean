-- Prove2me | solution 1 for lean_workbook_plus_23853
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:27.793484+00:00
-- url     : https://prove2.me/submissions/bc855838-0768-4784-98fe-3e7253a49a7b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (c : ℝ) : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ x : ℝ, x > N → |c - c| < ε := by
  (intros; simp_all)
