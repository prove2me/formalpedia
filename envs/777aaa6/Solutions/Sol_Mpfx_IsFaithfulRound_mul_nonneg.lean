-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.mul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:11:32.191514+00:00
-- url     : https://prove2.me/submissions/448b5f2d-1b21-4cca-aad0-1cf054fa273a

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_IsFaithfulRound_nonneg
import Theorems.Thm_Mpfx_IsFaithfulRound_nonpos

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hf : IsFaithfulRound F x z) : (z : ℝ) * x ≥ 0 := by
  rcases le_total 0 x with hx | hx
  · have hz := hf.nonneg hx
    positivity
  · exact mul_nonneg_of_nonpos_of_nonpos (hf.nonpos hx) hx
end IsFaithfulRound
end Mpfx
