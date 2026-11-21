-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_extend
-- name    : Mpfx.FiniteFormat.canonicalExp_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:32.547772+00:00
-- url     : https://prove2.me/theorems/ad2e5cc8-3403-4324-a944-108301708e07
-- title:
--   Finite Format: canonical Exp extend
-- statement:
--   Extending by `k` bits lowers the canonical exponent of every nonzero `x` by
--   exactly `k`: `p ↦ p + k` and `exp ↦ exp − k` each shift their term of the `max`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L519-L538
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L519-L538

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.canonicalExp_extend (F : FiniteFormat) (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (F.extend k).canonicalExp x = F.canonicalExp x - k := by sorry
