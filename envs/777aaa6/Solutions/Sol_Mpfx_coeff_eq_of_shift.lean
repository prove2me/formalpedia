-- Prove2me | solution 1 for Mpfx.coeff_eq_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:28:21.353881+00:00
-- url     : https://prove2.me/submissions/2b44cb19-80a9-4c19-bebe-0cc796dd4549

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Theorems.Thm_Mpfx_two_zpow_shift

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {K : Type*} [Field K] [CharZero K] {c₁ c₂ e₁ e₂ : ℤ} (h : e₁ ≤ e₂)
    (heq : (c₁ : K) * (2 : K) ^ e₁ = (c₂ : K) * (2 : K) ^ e₂) :
    c₁ = c₂ * (2 : ℤ) ^ (e₂ - e₁).toNat := by
  rw [two_zpow_shift c₂ h] at heq
  exact_mod_cast mul_right_cancel₀ (zpow_ne_zero _ two_ne_zero) heq
end Mpfx
