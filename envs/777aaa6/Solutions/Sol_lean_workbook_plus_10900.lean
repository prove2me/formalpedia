-- Prove2me | solution 1 for lean_workbook_plus_10900
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:16.464739+00:00
-- url     : https://prove2.me/submissions/23a594a4-cafc-43df-91ba-b1b96a8d3136

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (f_of : ∀ x < 0.5, f x = 2 * x) (f_on : ∀ x ≥ 0.5, f x = 2 - 2 * x) : ∀ x ∈ Set.Icc 0 1, f x ∈ Set.Icc 0 1 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
