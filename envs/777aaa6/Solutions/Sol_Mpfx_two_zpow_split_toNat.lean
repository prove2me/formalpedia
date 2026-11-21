-- Prove2me | solution 1 for Mpfx.two_zpow_split_toNat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:18:26.631682+00:00
-- url     : https://prove2.me/submissions/5ff2e5b4-d893-4365-9f55-aaf222c6754f

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {K : Type*} [Field K] [CharZero K] {e₁ e₂ : ℤ} (h : e₂ ≤ e₁) :
    (2 : K) ^ e₁ = (2 : K) ^ (e₁ - e₂).toNat * (2 : K) ^ e₂ := by
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, Int.toNat_of_nonneg (by omega)]
  congr 1; ring
end Mpfx
