-- Prove2me | solution 1 for lean_workbook_plus_40691
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:16:50.088388+00:00
-- url     : https://prove2.me/submissions/3766c79f-c7e7-409c-9301-5acb3c41668d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : 7 < 14) : (Nat.choose 7 2 : ℚ) / (Nat.choose 14 2 : ℚ) = 3 / 13 := by
  (intros; norm_num [Nat.factorial, Nat.choose])
