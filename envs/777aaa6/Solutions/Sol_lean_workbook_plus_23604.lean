-- Prove2me | solution 1 for lean_workbook_plus_23604
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:10.435385+00:00
-- url     : https://prove2.me/submissions/9c1dd450-ec5b-48e3-8a9d-da078dfc977b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, (a^2+b^2+c^2)^3 ≥ 27*a^2*b^2*c^2 := by
  intro a b c
  intros
  have h : (0 : ℝ) ≤ ((a^2+b^2+c^2)^3) - (27*a^2*b^2*c^2) := by
    calc
      0 ≤ (1 : ℝ) * (((c ^ 3) + ((-1) * c * (b ^ 2))))^2 + (1 : ℝ) * ((((-1) * (b ^ 3)) + (b * (c ^ 2))))^2 + (4 : ℝ) * (((b * (c ^ 2)) + ((-1) * b * (a ^ 2))))^2 + (4 : ℝ) * (((c * (b ^ 2)) + ((-1) * c * (a ^ 2))))^2 + ((5 / 2) : ℝ) * (((a * (c ^ 2)) + ((-1) * a * (b ^ 2))))^2 + ((1 / 2) : ℝ) * ((((-1) * (a ^ 3)) + (a * (c ^ 2))))^2 + ((1 / 2) : ℝ) * ((((-1) * (a ^ 3)) + (a * (b ^ 2))))^2 := by positivity
      _ = ((a^2+b^2+c^2)^3) - (27*a^2*b^2*c^2) := by ring
  exact sub_nonneg.mp h
