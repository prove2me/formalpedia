-- Prove2me | solution 1 for Fpy.DigitBound.LsbAt.le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:17:30.309954+00:00
-- url     : https://prove2.me/submissions/ad36c538-4935-47a3-99c2-9ebc70b6adbd

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
import Theorems.Thm_Mpfx_coeff_eq_of_shift


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace LsbAt
theorem _root_.solution {x : ℝ} {j k : ℤ} (hj : LsbAt x j) (hk : LsbAt x k) : j ≤ k := by
  obtain ⟨c, hc, rfl⟩ := hj
  obtain ⟨d, hd, he⟩ := hk
  by_contra hlt
  have := coeff_eq_of_shift (K := ℝ) (not_le.mp hlt).le he.symm
  have h2 : (2 : ℤ) ∣ d := this ▸ dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) c
  exact (Int.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr h2)
end LsbAt
end Fpy.DigitBound
