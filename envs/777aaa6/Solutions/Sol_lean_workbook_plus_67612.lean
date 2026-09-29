-- Prove2me | solution 1 for lean_workbook_plus_67612
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:48:44.90329+00:00
-- url     : https://prove2.me/submissions/d97ce323-c45d-4b96-a974-b3a19838ff87

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℚ) (h₁ : a = 5 / 19) (h₂ : b = 7 / 21) (h₃ : c = 9 / 23) : a < b ∧ b < c := by
  subst a
  subst b
  subst c
  norm_num
