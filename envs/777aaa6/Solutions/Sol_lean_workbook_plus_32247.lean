-- Prove2me | solution 1 for lean_workbook_plus_32247
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:28.25426+00:00
-- url     : https://prove2.me/submissions/3d5ef165-8c4c-4fb4-950c-591f534ffd86

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : x^2 - 4*x >= 0 ↔ x ≤ 0 ∨ x ≥ 4 := by
  constructor
  · intro h
    by_cases hx : x≤0
    · exact Or.inl hx
    · right
      by_contra hn
      have hp := mul_neg_of_pos_of_neg (show 0<x by linarith) (show x-4<0 by linarith)
      nlinarith
  · rintro (h|h)
    · have hp := mul_nonneg_of_nonpos_of_nonpos h (show x-4≤0 by linarith)
      nlinarith
    · have hp := mul_nonneg (show 0≤x by linarith) (show 0≤x-4 by linarith)
      nlinarith
