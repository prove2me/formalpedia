-- Prove2me | solution 1 for lean_workbook_plus_34190
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:16.188665+00:00
-- url     : https://prove2.me/submissions/531bd1a6-dbd1-4000-bd68-754c6e0aa06f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x p : ℝ)
  (h₀ : 0 < x ∧ 0 < p)
  (h₁ : (1 + p / 100) * (1 - p / 100) * x = 1) :
  x = 10000 / (10000 - p^2) := by
  intros
  grind
