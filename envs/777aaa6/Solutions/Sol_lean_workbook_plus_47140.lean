-- Prove2me | solution 1 for lean_workbook_plus_47140
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:09:24.29123+00:00
-- url     : https://prove2.me/submissions/8f901243-f947-4b5d-bc5a-3bea35e7f07d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) (hn : Odd n) : 11 ∣ (10 ^ n + (- 1) ^ (n + 1)) := by
  have h := (show (10:ℤ) ≡ -1 [ZMOD 11] from by norm_num [Int.ModEq]).pow n
  apply Int.modEq_zero_iff_dvd.mp
  have hh := h.add (Int.ModEq.refl ((-1:ℤ)^(n+1)))
  convert hh using 1
  rw [pow_succ]
  ring
