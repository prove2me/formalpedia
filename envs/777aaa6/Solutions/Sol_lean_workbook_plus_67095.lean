-- Prove2me | solution 1 for lean_workbook_plus_67095
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:55.506228+00:00
-- url     : https://prove2.me/submissions/00d92a5c-236b-4b0a-a8c2-32fdb06d610e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : (x^6 + x^3*y^3 + y^6) ≤ (3/2)*(x^6 + y^6) := by
  intros
  have h : (0 : ℝ) ≤ ((3/2)*(x^6 + y^6)) - ((x^6 + x^3*y^3 + y^6)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((y ^ 3) + ((-1) * (x ^ 3))))^2 := by positivity
      _ = ((3/2)*(x^6 + y^6)) - ((x^6 + x^3*y^3 + y^6)) := by ring
  exact sub_nonneg.mp h
