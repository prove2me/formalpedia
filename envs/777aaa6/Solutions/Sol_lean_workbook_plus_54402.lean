-- Prove2me | solution 1 for lean_workbook_plus_54402
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:55.304708+00:00
-- url     : https://prove2.me/submissions/99924e54-d7c7-4f89-ae25-70d8096b4570

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + a * c + b * c := by
  intros
  have h : (0 : ℝ) ≤ (a ^ 2 + b ^ 2 + c ^ 2) - (a * b + a * c + b * c) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((c + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((c + ((-1) * a)))^2 + ((1 / 2) : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (a ^ 2 + b ^ 2 + c ^ 2) - (a * b + a * c + b * c) := by ring
  exact sub_nonneg.mp h
