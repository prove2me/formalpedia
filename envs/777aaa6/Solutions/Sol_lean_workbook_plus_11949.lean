-- Prove2me | solution 1 for lean_workbook_plus_11949
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:05.562897+00:00
-- url     : https://prove2.me/submissions/c63ab515-fc9b-4d48-8ba8-c7862aa3d7f9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution :
  ∀ b c : ℝ, b ≥ 0 ∧ c ≥ 0 → (b + c)^2 ≥ 4 * b * c := by
  intro b c
  intros
  have h : (0 : ℝ) ≤ ((b + c)^2) - (4 * b * c) := by
    calc
      0 ≤ (1 : ℝ) * ((c + ((-1) * b)))^2 := by positivity
      _ = ((b + c)^2) - (4 * b * c) := by ring
  exact sub_nonneg.mp h
