-- Prove2me | solution 1 for lean_workbook_plus_5026
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:18.975058+00:00
-- url     : https://prove2.me/submissions/cbd18b0a-861f-4e1e-ac96-55524ab0e9cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : 40 - 33.5 = 6.5) : 40 - 33.5 = 6.5 := by
  (intros; simp_all)
