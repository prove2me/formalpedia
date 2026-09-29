-- Prove2me | solution 1 for lean_workbook_plus_57856
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:36.225738+00:00
-- url     : https://prove2.me/submissions/1c7ac31b-f1f9-4950-8c37-3e4e5069e7c5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h1 : 2 < a) (h2 : 2 < b) (h3 : 2 < c) : a + b + c < a * b * c := by
  have ha : 0 < a-2 := sub_pos.mpr h1
  have hb : 0 < b-2 := sub_pos.mpr h2
  have hc : 0 < c-2 := sub_pos.mpr h3
  have h1p : 0 ≤ (a-2)*(b-2) := by positivity
  have h2p : 0 ≤ (b-2)*(c-2) := by positivity
  have h3p : 0 ≤ (c-2)*(a-2) := by positivity
  have h4p : 0 ≤ (a-2)*(b-2)*(c-2) := by positivity
  nlinarith only [h1p,h2p,h3p,h4p,h1,h2,h3]
