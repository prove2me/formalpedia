-- Prove2me | solution 1 for lean_workbook_plus_47740
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:36.081169+00:00
-- url     : https://prove2.me/submissions/a4d1e31d-6196-4672-bd46-e2529f2ff3e1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2)^2 ≥ (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b) := by
  intros
  have h : (0 : ℝ) ≤ ((a^2 + b^2)^2) - ((a + b + c) * (a + b - c) * (b + c - a) * (c + a - b)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((c ^ 2) + ((-2) * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (((c ^ 2) + ((-2) * (a ^ 2))))^2 := by positivity
      _ = ((a^2 + b^2)^2) - ((a + b + c) * (a + b - c) * (b + c - a) * (c + a - b)) := by ring
  exact sub_nonneg.mp h
