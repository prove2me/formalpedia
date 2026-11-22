-- Prove2me | solution 1 for Fpy.RoundCtx.round_of_not_overflows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:40:22.974976+00:00
-- url     : https://prove2.me/submissions/cd3531d7-a87a-48cf-8996-9047b7c8d3f3

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
import Theorems.Thm_Fpy_RoundCtx_round_unbounded
import Theorems.Thm_Fpy_RoundCtx_round_finite
import Theorems.Thm_Mpfx_rndUnbounded_satisfies


set_option autoImplicit true
open Fpy
open Mpfx
open Fpy.RoundCtx
namespace Fpy.RoundCtx
theorem _root_.solution {c c' : RoundCtx} (hF : c'.F = c.F.unbounded) (hrm : c'.rm = c.rm)
    {y : ℝ} (h : ¬ Overflows c.F c.rm y) : c'.round (.finite y) = c.round (.finite y) := by
  rw [round_unbounded hF hrm, round_finite, if_pos]
  by_contra hb
  exact h ⟨_, rndUnbounded_satisfies c.F c.rm y c.defined, hb⟩
end Fpy.RoundCtx
