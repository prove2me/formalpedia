-- Prove2me | solution 1 for lean_workbook_plus_35956
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:04.458996+00:00
-- url     : https://prove2.me/submissions/5f6dee6e-a5ec-4b27-b535-360d4e42079c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : 3 * (a ^ 4 * b ^ 2 * c ^ 2 + b ^ 4 * c ^ 2 * a ^ 2 + c ^ 4 * a ^ 2 * b ^ 2) ≤ a ^ 4 * b ^ 4 + b ^ 4 * c ^ 4 + c ^ 4 * a ^ 4 + 2 * (a ^ 4 * b ^ 2 * c ^ 2 + b ^ 4 * c ^ 2 * a ^ 2 + c ^ 4 * a ^ 2 * b ^ 2) := by
  intros
  have h : (0 : ℝ) ≤ (a ^ 4 * b ^ 4 + b ^ 4 * c ^ 4 + c ^ 4 * a ^ 4 + 2 * (a ^ 4 * b ^ 2 * c ^ 2 + b ^ 4 * c ^ 2 * a ^ 2 + c ^ 4 * a ^ 2 * b ^ 2)) - (3 * (a ^ 4 * b ^ 2 * c ^ 2 + b ^ 4 * c ^ 2 * a ^ 2 + c ^ 4 * a ^ 2 * b ^ 2)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((((b ^ 2) * (c ^ 2)) + ((-1) * (a ^ 2) * (c ^ 2))))^2 + ((1 / 2) : ℝ) * ((((b ^ 2) * (c ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2))))^2 + ((1 / 2) : ℝ) * ((((a ^ 2) * (c ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2))))^2 := by positivity
      _ = (a ^ 4 * b ^ 4 + b ^ 4 * c ^ 4 + c ^ 4 * a ^ 4 + 2 * (a ^ 4 * b ^ 2 * c ^ 2 + b ^ 4 * c ^ 2 * a ^ 2 + c ^ 4 * a ^ 2 * b ^ 2)) - (3 * (a ^ 4 * b ^ 2 * c ^ 2 + b ^ 4 * c ^ 2 * a ^ 2 + c ^ 4 * a ^ 2 * b ^ 2)) := by ring
  exact sub_nonneg.mp h
