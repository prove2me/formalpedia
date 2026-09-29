-- Prove2me | solution 1 for lean_workbook_plus_25000
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:46:28.206382+00:00
-- url     : https://prove2.me/submissions/f6659f3a-52b4-4151-adf8-e9b6303bc249

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p k : ℕ) (x : Units (ZMod (p^k))) (hx : x^6 = 1) :
    orderOf x ∣ 6 := by
  intros
  exact orderOf_dvd_of_pow_eq_one hx
