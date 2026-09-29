-- Prove2me | solution 1 for lean_workbook_plus_1939
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:24:29.284704+00:00
-- url     : https://prove2.me/submissions/e4d9e108-14e4-4ac7-841b-d0cacdea6d3d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (k : ℕ) : (3^(3^k - k) % 3) = 0 := by
  have hk : k < 3^k := Nat.lt_pow_self (by decide)
  have he : 0 < 3^k-k := Nat.sub_pos_of_lt hk
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_self (3:ℕ) (ne_of_gt he))
