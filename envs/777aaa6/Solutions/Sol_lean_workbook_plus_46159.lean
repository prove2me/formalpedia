-- Prove2me | solution 1 for lean_workbook_plus_46159
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:32.915457+00:00
-- url     : https://prove2.me/submissions/82fc095b-b4ea-4a38-bdcf-dffa6487ccd7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a r : ℂ) :
  (a / (1 - r)) * (a / (1 + r)) = a^2 / (1 - r^2) := by
  (intros; field_simp; ring)
