-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:10:21.712531+00:00
-- url     : https://prove2.me/submissions/fa2bca9c-1f8d-4ef1-8f68-01b1a9cd1ed8

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_isFaithfulRound_iff_directed
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_nonpos

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hf : IsFaithfulRound F x z) (hx : x ≤ 0) : (z : ℝ) ≤ 0 := by
  rcases isFaithfulRound_iff_directed.mp hf with hd | hu
  · exact hd.2.1.trans hx
  · exact RoundsFinite.toPositive_nonpos hx hu
end IsFaithfulRound
end Mpfx
