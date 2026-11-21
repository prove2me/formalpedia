-- Prove2me | solution 1 for Mpfx.FiniteFormat.p_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:25:31.290575+00:00
-- url     : https://prove2.me/submissions/7af005a8-3d13-479f-b097-17a2f6b03902

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution {F : FiniteFormat} {p : ℕ} (hp : F.p = (p : Prec)) : 0 < p := by
  rcases Nat.eq_zero_or_pos p with rfl | h
  · exact absurd hp F.pos
  · exact h
end Mpfx.FiniteFormat
