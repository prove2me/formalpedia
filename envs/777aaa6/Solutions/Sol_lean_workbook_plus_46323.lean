-- Prove2me | solution 1 for lean_workbook_plus_46323
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:09:23.160716+00:00
-- url     : https://prove2.me/submissions/56020005-6d02-43b0-bc2b-5466fb39b28b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n a : ℤ) (hn : n > 0) : gcd a (a + n) ∣ n := by
  have h := dvd_sub (gcd_dvd_right a (a+n)) (gcd_dvd_left a (a+n))
  simpa only [add_sub_cancel_left] using h
