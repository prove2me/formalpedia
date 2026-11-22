-- Prove2me | solution 1 for Mpfx.rnd_of_overflows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:34:38.269773+00:00
-- url     : https://prove2.me/submissions/6cc415aa-bfec-4610-8431-1dfce423964f

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
import Theorems.Thm_Mpfx_rnd_finite_of_roundsFinite
import Theorems.Thm_Mpfx_IsFaithfulRound_decide_lt_zero
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_ne_zero_of_not_boundOK


set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {S : SpecialMap F.toFormat}
    {O : OverflowMap F.toFormat} {rm : RoundingMode} {x : ℝ}
    (h : ¬ F.IsUndefined rm) (hov : Overflows F rm x) :
    rnd F S O rm (.finite x) = .value (O.map (decide (x < 0))) := by
  obtain ⟨y, hy, hnb⟩ := hov
  rw [rnd_finite_of_roundsFinite h hy, if_neg hnb,
    hy.isFaithfulRound.decide_lt_zero (ne_zero_of_not_boundOK hnb)]
end Mpfx
