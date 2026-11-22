-- Prove2me | Theorems.Thm_Fpy_rndInt_congr
-- name    : Fpy.rndInt_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:32:58.655772+00:00
-- url     : https://prove2.me/theorems/bcc7a67b-3b87-4762-9123-a2b02f445392
-- title:
--   Fpy: rnd Int congr
-- statement:
--   The integer step agrees on two inputs with the same scaled mantissa and
--   sign, when the formats agree on the parity of the floor point off the grid.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L34-L76
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L34-L76

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.rndInt_congr {F G : FiniteFormat} {rm : RoundingMode} {x x' : ℝ} {e e' : ℤ}
    (hs : x' * (2 : ℝ) ^ (-e') = x * (2 : ℝ) ^ (-e)) (hx : 0 ≤ x' ↔ 0 ≤ x)
    (hodd : (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-e) →
      (G.IsOdd (Mpfx.Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-e)⌋ e') ↔
        F.IsOdd (Mpfx.Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-e)⌋ e)))
    (heven : (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-e) →
      (G.IsEven (Mpfx.Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-e)⌋ e') ↔
        F.IsEven (Mpfx.Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-e)⌋ e))) :
    rndInt G rm x' e' = rndInt F rm x e := by sorry
