-- Prove2me | solution 1 for lean_workbook_plus_40203
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:16.521417+00:00
-- url     : https://prove2.me/submissions/aa48d122-3492-4336-b28b-efd5784a3aa8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (S E I : ℝ) : S / (E + I) = 25 → E + I = S / 25 := by
  intro h
  have hd : E+I ≠ 0 := by intro hz; simp [hz] at h
  have he := (div_eq_iff hd).mp h
  linarith
