-- Prove2me | solution 1 for lean_workbook_plus_6940
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:14.493429+00:00
-- url     : https://prove2.me/submissions/5c1b98bf-6d84-4a06-ab49-bece0ee58957

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : a^8 + b^8 ≥ (a^4 + b^4)^2 / 2 := by
  intros
  have h : (0 : ℝ) ≤ (a^8 + b^8) - ((a^4 + b^4)^2 / 2) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((b ^ 4) + ((-1) * (a ^ 4))))^2 := by positivity
      _ = (a^8 + b^8) - ((a^4 + b^4)^2 / 2) := by ring
  exact sub_nonneg.mp h
