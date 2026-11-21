-- Prove2me | solution 1 for Mpfx.Dyadic.IsRepresentableAtP.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:25:41.458115+00:00
-- url     : https://prove2.me/submissions/77d4ee4e-2760-46a0-8554-af916a2fd384

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
namespace IsRepresentableAtP
theorem _root_.solution {n : ℕ} {c e : ℤ} {y : Dyadic}
    (h : IsRepresentableAtP n c e y) : (y : ℚ) ≠ 0 := by
  obtain ⟨hyeq, hc_lo, _⟩ := h
  intro h0; rw [h0] at hyeq
  have h2e_pos : (0 : ℚ) < (2 : ℚ) ^ e := zpow_pos (by norm_num) _
  have hc_zero : (c : ℚ) = 0 := by
    rcases mul_eq_zero.mp hyeq.symm with h | h
    · exact h
    · linarith
  have hc_zero_int : c = 0 := by exact_mod_cast hc_zero
  rw [hc_zero_int, abs_zero] at hc_lo
  have hpos : (1 : ℤ) ≤ (2 : ℤ) ^ (n - 1) := one_le_pow₀ (by norm_num)
  linarith
end IsRepresentableAtP
end Mpfx.Dyadic
