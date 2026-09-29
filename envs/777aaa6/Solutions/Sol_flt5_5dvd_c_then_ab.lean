-- Prove2me | solution 1 for flt5_5dvd_c_then_ab
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:11:33.118507+00:00
-- url     : https://prove2.me/submissions/bdeb8943-3fa2-436a-a142-982927d3a825

import Theorems.Thm_flt5_5dvd_c_then_ab
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

-- If a^5+b^5=c^5 and 5|c, then 5|(a+b).
-- By Fermat in ZMod 5: x^5 = x, so a+b ≡ a^5+b^5 = c^5 ≡ 0 (mod 5).

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h5c : (5 : ℤ) ∣ c) :
    (5 : ℤ) ∣ a + b := by
  have fermat : ∀ x : ZMod 5, x ^ 5 = x := by decide
  have hc : ((c : ℤ) : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd c 5).mpr h5c
  have hab : ((a + b : ℤ) : ZMod 5) = 0 := by
    have step : ((a ^ 5 + b ^ 5 : ℤ) : ZMod 5) = ((c ^ 5 : ℤ) : ZMod 5) :=
      congrArg (Int.cast) h_eq
    push_cast at step ⊢
    simp only [fermat] at step
    rw [hc] at step
    simpa using step
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 5).mp hab
