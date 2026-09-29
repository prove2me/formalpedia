-- Prove2me | solution 1 for lean_workbook_plus_53847
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:06:02.89141+00:00
-- url     : https://prove2.me/submissions/765cb752-9910-42e5-9873-1205251c35b7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : (x - 1) * (y - 1) ≥ 1) : x * y ≥ x + y := by
  (intros; linarith)
