-- Prove2me | Theorems.Thm_Mpfx_neighbor_abs_le
-- name    : Mpfx.neighbor_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:22.927671+00:00
-- url     : https://prove2.me/theorems/00b793da-8a08-4da7-a1fe-8665427e3a87
-- title:
--   Mpfx: neighbor abs le
-- statement:
--   A neighbour of `x` at the canonical step has significand at most `2^p`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Parity.lean#L54-L61
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Parity.lean#L54-L61

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Parity
set_option autoImplicit true
open Mpfx

theorem Mpfx.neighbor_abs_le {F : FiniteFormat} (x : ℝ) {m : ℤ}
    (hm : m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ ∨
      m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) {p : ℕ} (hp : F.p = p) :
    |m| ≤ 2 ^ p := by sorry
