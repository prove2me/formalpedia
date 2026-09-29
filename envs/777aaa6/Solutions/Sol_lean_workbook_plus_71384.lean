-- Prove2me | solution 1 for lean_workbook_plus_71384
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:35:10.706698+00:00
-- url     : https://prove2.me/submissions/549395d2-09e2-4743-90c8-13800051bb5f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.GCDMonoid.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (a b : ℤ) (h : a > b) : gcd a b = gcd (a - b) b := by
  apply gcd_eq_of_dvd_sub_left
  convert dvd_refl b using 1 <;> ring
