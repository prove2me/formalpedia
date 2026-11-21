-- Prove2me | solution 1 for Mpfx.isFaithfulRound_iff_directed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:43:49.729754+00:00
-- url     : https://prove2.me/submissions/2e9eda05-34f4-4700-9baf-0b44a8dcc9f6

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {y : Dyadic} :
    IsFaithfulRound F x y ↔
      RoundsFinite F .toNegative x y ∨ RoundsFinite F .toPositive x y :=
  Iff.rfl
end Mpfx
