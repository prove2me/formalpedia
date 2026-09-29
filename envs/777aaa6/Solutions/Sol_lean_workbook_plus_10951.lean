-- Prove2me | solution 1 for lean_workbook_plus_10951
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:05:53.356676+00:00
-- url     : https://prove2.me/submissions/6c104f0f-f619-4115-a448-e71e1baeb262

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ y : ℤ, y^2 % 8 = 0 → y^2 % 16 = 0 := by
  intro y hy
  have hr := (Int.mod_modEq y 16).pow 2
  have hr8 := hr.of_dvd (by decide : (8 : ℤ) ∣ 16)
  change (y % 16) ^ 2 % 16 = y ^ 2 % 16 at hr
  change (y % 16) ^ 2 % 8 = y ^ 2 % 8 at hr8
  have hlo := Int.emod_nonneg y (by decide : (16 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos y (by decide : (0 : ℤ) < 16)
  interval_cases he : y % 16 <;> norm_num [he] at hr hr8 <;> omega
