-- Prove2me | solution 1 for lean_workbook_plus_65854
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:37.502546+00:00
-- url     : https://prove2.me/submissions/92436c5b-eec8-486e-95d4-51023de32ee5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (hx: a + b >= c) (hb: b + c >= a) (hc: a + c >= b) : a + b >= c ∧ b + c >= a ∧ a + c >= b := by
  (intros; simp_all)
