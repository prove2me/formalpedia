-- Prove2me | solution 1 for Fpy.DigitBound.abs_le_of_grid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:42:59.451552+00:00
-- url     : https://prove2.me/submissions/9394d6da-8b56-4002-9050-5e6dca5965f9

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
import Theorems.Thm_Fpy_DigitBound_LsbAt_le


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {Ψ : List Con} {ι : Asgn} {l m : Term} {τ : Option Term} {x : ℝ}
namespace Fpy.DigitBound
theorem _root_.solution {c lo k : ℤ} (h : |(c : ℝ) * 2 ^ lo| < 2 ^ (k + 1)) (hlo : lo ≤ k) :
    |(c : ℝ) * 2 ^ lo| ≤ 2 ^ (k + 1) - 2 ^ lo := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k + 1 = lo + n := ⟨(k + 1 - lo).toNat, by omega⟩
  have hp : (0 : ℝ) < 2 ^ lo := zpow_pos two_pos lo
  rw [abs_mul, abs_of_pos hp, hn, zpow_add₀ two_ne_zero, zpow_natCast] at h ⊢
  have hc : |c| < 2 ^ n := by
    have : |(c : ℝ)| < 2 ^ n := lt_of_mul_lt_mul_right (by linarith) hp.le
    exact_mod_cast this
  have hc' : (|c| : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hc
  nlinarith [mul_le_mul_of_nonneg_right hc' hp.le, Int.cast_abs (R := ℝ) (a := c)]
end Fpy.DigitBound
