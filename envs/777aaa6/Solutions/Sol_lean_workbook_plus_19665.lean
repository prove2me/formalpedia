-- Prove2me | solution 1 for lean_workbook_plus_19665
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:54.897004+00:00
-- url     : https://prove2.me/submissions/c80f5837-c094-4ebc-b2cb-882726128fd6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (hf : ∀ x, f x + f (x + 1 / 2) = 0) :
  ∀ x, f x = f (x + 1) := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
