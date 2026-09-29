-- Prove2me | solution 1 for lean_workbook_plus_3566
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:01.013734+00:00
-- url     : https://prove2.me/submissions/b59832eb-1838-4a35-afd8-511a4659d823

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (T : ℕ → ℝ) (h₁ : T 0 = 212) (h₂ : ∀ n, T (n + 5) = (T n + 68) / 2) : T 15 = 86 := by
  intros
  grind
