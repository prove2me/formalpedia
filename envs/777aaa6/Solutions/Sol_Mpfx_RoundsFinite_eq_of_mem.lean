-- Prove2me | solution 1 for Mpfx.RoundsFinite.eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:15:04.768303+00:00
-- url     : https://prove2.me/submissions/fe2fd40b-511b-4883-9b38-29962d3f956d

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_of_mem
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} {d : Dyadic}
    (hd : d ∈ F) {y : Dyadic} (h : RoundsFinite F rm (d : ℝ) y) : y = d :=
  h.isFaithfulRound.eq_of_mem hd
end RoundsFinite
end Mpfx
