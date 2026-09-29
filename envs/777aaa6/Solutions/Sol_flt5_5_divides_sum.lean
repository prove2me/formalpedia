-- Prove2me | solution 1 for flt5_5_divides_sum
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T10:46:31.927648+00:00
-- url     : https://prove2.me/submissions/9deeff75-cc1a-4b7e-bea4-c5735cbfd7ce

import Theorems.Thm_flt5_5_divides_sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h5c : (5 : ℤ) ∣ c) :
    (5 : ℤ) ∣ a + b := by
  -- Fermat's little theorem in ZMod 5: x^5 = x for all x
  have key5 : ∀ x : ZMod 5, x ^ 5 = x := by decide
  -- Cast equation to ZMod 5
  have heq5 : ((a : ℤ) : ZMod 5) ^ 5 + ((b : ℤ) : ZMod 5) ^ 5 = ((c : ℤ) : ZMod 5) ^ 5 := by
    have := congr_arg (Int.cast : ℤ → ZMod 5) h_eq
    push_cast at this; exact this
  -- c ≡ 0 (mod 5)
  have hc0 : ((c : ℤ) : ZMod 5) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h5c
  -- Apply Fermat: a + b ≡ a^5 + b^5 = c^5 ≡ 0 (mod 5)
  have hab : ((a : ℤ) : ZMod 5) + ((b : ℤ) : ZMod 5) = 0 := by
    simp only [key5, hc0, zero_pow (show 5 ≠ 0 from by omega)] at heq5
    exact heq5
  -- Lift to ℤ divisibility
  have hlift : ((a + b : ℤ) : ZMod 5) = 0 := by push_cast; exact hab
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hlift
