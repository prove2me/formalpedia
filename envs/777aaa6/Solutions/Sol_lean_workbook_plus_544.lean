-- Prove2me | solution 1 for lean_workbook_plus_544
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:42.342437+00:00
-- url     : https://prove2.me/submissions/c001f006-e25a-491e-be4c-c06265e65e7a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (h : ∀ x, f x ^ 2 = 1) : Set.range f ⊆ {1, -1} := by
  intros
  grind
