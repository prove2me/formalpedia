-- Prove2me | solution 1 for flt7_sum_dvd_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T07:41:22.389537+00:00
-- url     : https://prove2.me/submissions/169fc1d2-2530-4bbb-985a-ed937ca64895

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

-- 7 | (a+b) when a^7 + b^7 = c^7 and 7 | c.
-- Proof: By Fermat's little theorem, x^7 = x in ZMod 7.
-- So a + b ≡ a^7 + b^7 = c^7 ≡ c ≡ 0 (mod 7).
theorem solution (a b c : ℤ) (h_eq : a ^ 7 + b ^ 7 = c ^ 7) (h7c : (7 : ℤ) ∣ c) :
    (7 : ℤ) ∣ a + b := by
  have hfermat : ∀ x : ZMod 7, x ^ 7 = x := by decide
  have hc : (c : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd c 7).mpr h7c
  have heq7 : (a : ZMod 7) ^ 7 + (b : ZMod 7) ^ 7 = (c : ZMod 7) ^ 7 := by
    have h := congr_arg (Int.cast : ℤ → ZMod 7) h_eq
    push_cast at h
    exact h
  have hab0 : ((a + b : ℤ) : ZMod 7) = 0 := by
    push_cast
    calc (a : ZMod 7) + b
        = (a : ZMod 7) ^ 7 + (b : ZMod 7) ^ 7 := by
            rw [hfermat (a : ZMod 7), hfermat (b : ZMod 7)]
      _ = (c : ZMod 7) ^ 7 := heq7
      _ = (c : ZMod 7) := hfermat _
      _ = 0 := hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 7).mp hab0
