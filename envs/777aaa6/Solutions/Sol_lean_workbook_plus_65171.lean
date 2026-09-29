-- Prove2me | solution 1 for lean_workbook_plus_65171
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:41.316844+00:00
-- url     : https://prove2.me/submissions/cbd30802-24c8-42e3-b6ab-bdbcb133d409

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (f : ℝ → ℝ) (hf: f 0 = 2) (h : ∀ x, f x + (f x) * (f 0) = f 0 + f x + f 0) : f x = 2 := by
  intros
  grind
