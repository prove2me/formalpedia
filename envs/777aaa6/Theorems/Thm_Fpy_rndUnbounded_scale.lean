-- Prove2me | Theorems.Thm_Fpy_rndUnbounded_scale
-- name    : Fpy.rndUnbounded_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:33:58.340849+00:00
-- url     : https://prove2.me/theorems/ce6897fb-a466-4e79-813f-4011914676c7
-- title:
--   Fpy: rnd Unbounded scale
-- statement:
--   Rounding into `𝒜(∞, k)` is `2ᵏ` times rounding `2⁻ᵏx` into `𝒜(∞, 0)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L102-L129
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L102-L129

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.rndUnbounded_scale {F G : FiniteFormat} {rm : RoundingMode} {k : ℤ}
    (hFp : F.p = ⊤) (hFe : F.exp = (k : QExp)) (hGp : G.p = ⊤) (hGe : G.exp = ((0 : ℤ) : QExp))
    (x : ℝ) (hF : ¬ F.IsUndefined rm) (hG : ¬ G.IsUndefined rm) :
    ((rndUnbounded F rm x hF : Mpfx.Dyadic) : ℝ) =
      2 ^ k * (rndUnbounded G rm (2 ^ (-k) * x) hG : Mpfx.Dyadic) := by sorry
