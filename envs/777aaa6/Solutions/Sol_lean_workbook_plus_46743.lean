-- Prove2me | solution 1 for lean_workbook_plus_46743
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:01.862214+00:00
-- url     : https://prove2.me/submissions/4628d995-2de2-4c04-8142-bd76f4e20ad0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (c : ℝ) : (1 + c^2) / 2 ≥ c := by
  intros
  have h : (0 : ℝ) ≤ ((1 + c^2) / 2) - (c) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * c)))^2 := by positivity
      _ = ((1 + c^2) / 2) - (c) := by ring
  exact sub_nonneg.mp h
