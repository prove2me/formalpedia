-- Prove2me | solution 1 for euler_phi5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:26:55.85885+00:00
-- url     : https://prove2.me/submissions/8e78a8d4-2cb6-4161-a9ee-75fb23d6aac6

import Theorems.Thm_euler_phi5
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (a : ℤ) (h : ¬(5 : ℤ) ∣ a) : (5 : ℤ) ∣ a ^ 4 - 1 := by
  have key : ∀ x : ZMod 5, x ≠ 0 → x ^ 4 = 1 := by decide
  have ha_nz : (a : ZMod 5) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h4 : ((a ^ 4 - 1 : ℤ) : ZMod 5) = 0 := by
    push_cast
    rw [key _ ha_nz, sub_self]
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h4
