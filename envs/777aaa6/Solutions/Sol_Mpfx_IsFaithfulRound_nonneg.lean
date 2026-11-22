-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:09:40.338493+00:00
-- url     : https://prove2.me/submissions/ce45d443-f55b-4052-894c-36998021cfa4

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_isFaithfulRound_iff_directed
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_nonneg

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hf : IsFaithfulRound F x z) (hx : 0 ≤ x) : 0 ≤ (z : ℝ) := by
  rcases isFaithfulRound_iff_directed.mp hf with hd | hu
  · exact RoundsFinite.toNegative_nonneg hx hd
  · exact hx.trans hu.2.1
end IsFaithfulRound
end Mpfx
