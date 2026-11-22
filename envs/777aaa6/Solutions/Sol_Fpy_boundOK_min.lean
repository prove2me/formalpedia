-- Prove2me | solution 1 for Fpy.boundOK_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:45.910334+00:00
-- url     : https://prove2.me/submissions/b2177996-8f4c-4435-9228-b8781d6bae11

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine

set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}
namespace Fpy
theorem _root_.solution {b : Bound} {d : NonNegDyadic} {x : Mpfx.Dyadic} (hb : Format.boundOK b x)
    (hx : |(x : ℚ)| ≤ ((d.1 : Mpfx.Dyadic) : ℚ)) : Format.boundOK (min b ↑d) x := by
  rcases min_choice b ↑d with h | h <;> rw [h]
  · exact hb
  · exact hx
end Fpy
