-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.decide_lt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:10:22.252151+00:00
-- url     : https://prove2.me/submissions/c8efed79-22b1-415d-93d1-32dac26ec52d

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_isFaithfulRound_iff_directed
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_nonneg
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_nonpos
import Theorems.Thm_Mpfx_Dyadic_coe_real_lt_zero_iff


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {y : Dyadic}
    (h : IsFaithfulRound F x y) (hy : (y : ℝ) ≠ 0) :
    decide ((y : ℚ) < 0) = decide (x < 0) := by
  have key : (y : ℝ) < 0 ↔ x < 0 := by
    rcases isFaithfulRound_iff_directed.mp h with hd | hu
    · refine ⟨fun hy0 => ?_, fun hx => lt_of_le_of_lt hd.2.1 hx⟩
      by_contra hx
      linarith [RoundsFinite.toNegative_nonneg (not_lt.mp hx) hd]
    · refine ⟨fun hy0 => lt_of_le_of_lt hu.2.1 hy0, fun hx => ?_⟩
      exact lt_of_le_of_ne (RoundsFinite.toPositive_nonpos hx.le hu) hy
  rw [decide_eq_decide, ← key, Dyadic.coe_real_lt_zero_iff]
end IsFaithfulRound
end Mpfx
