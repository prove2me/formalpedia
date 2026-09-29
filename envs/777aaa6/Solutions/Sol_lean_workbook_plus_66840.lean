-- Prove2me | solution 1 for lean_workbook_plus_66840
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:40.450281+00:00
-- url     : https://prove2.me/submissions/0edcb65b-b244-441c-85be-0c210813fe78

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2*c + b^2*a + c^2*b - a^2*b - b^2*c - c^2*a) = (b - a)*(c - a)*(c - b) := by
  (intros; linarith)
