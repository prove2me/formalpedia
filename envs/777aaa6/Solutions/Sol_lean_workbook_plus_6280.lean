-- Prove2me | solution 1 for lean_workbook_plus_6280
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:36.809239+00:00
-- url     : https://prove2.me/submissions/8cd15dba-5594-488b-825c-01f47a774b90

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : (3 : ℝ)^( (-3:ℤ)/4 ) > 4^( (-5:ℤ)/6 ) := by
  norm_num
