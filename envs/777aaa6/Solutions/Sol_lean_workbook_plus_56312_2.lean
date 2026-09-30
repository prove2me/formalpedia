-- Prove2me | solution 2 for lean_workbook_plus_56312
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:20.559843+00:00
-- url     : https://prove2.me/submissions/aa09965f-10bf-49cc-b818-d9bb248e930b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : (a^4 + 1) * (b^4 + 1) ≥ (a^2 + b^2)^2 := by
  intros
  have h : (0 : ℝ) ≤ ((a^4 + 1) * (b^4 + 1)) - ((a^2 + b^2)^2) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * (a ^ 2) * (b ^ 2))))^2 := by positivity
      _ = ((a^4 + 1) * (b^4 + 1)) - ((a^2 + b^2)^2) := by ring
  exact sub_nonneg.mp h
