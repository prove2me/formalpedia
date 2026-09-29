-- Prove2me | solution 1 for lean_workbook_plus_43801
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:59.68212+00:00
-- url     : https://prove2.me/submissions/9b576851-79fe-48db-bb60-d70c96cd3f52

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : gcd a b ∣ lcm a b := by
  exact (gcd_dvd_left a b).trans (dvd_lcm_left a b)
