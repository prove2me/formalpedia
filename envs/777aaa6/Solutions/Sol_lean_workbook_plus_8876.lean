-- Prove2me | solution 1 for lean_workbook_plus_8876
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:48.891176+00:00
-- url     : https://prove2.me/submissions/6bfd3013-0d57-4ba9-8fd6-a3f54cba7628

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : f 1 = a)
  (h₁ : f a = -1)
  (h₂ : f (-1) = -a)
  (h₃ : f (-a) = 1) :
  a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
