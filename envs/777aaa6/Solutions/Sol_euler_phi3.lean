-- Prove2me | solution 1 for euler_phi3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:26:55.354643+00:00
-- url     : https://prove2.me/submissions/66f4b5f1-c080-456a-9037-ae410910d2fa

import Theorems.Thm_euler_phi3
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (a : ℤ) (h : ¬(3 : ℤ) ∣ a) : (3 : ℤ) ∣ a ^ 2 - 1 := by
  have key : ∀ x : ZMod 3, x ≠ 0 → x ^ 2 = 1 := by decide
  have ha_nz : (a : ZMod 3) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 : ((a ^ 2 - 1 : ℤ) : ZMod 3) = 0 := by
    push_cast
    rw [key _ ha_nz, sub_self]
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
