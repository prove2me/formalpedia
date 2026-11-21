-- Prove2me | Theorems.Thm_Mpfx_ulp_eq_zpow_of
-- name    : Mpfx.ulp_eq_zpow_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:46:17.540964+00:00
-- url     : https://prove2.me/theorems/a0849006-628d-4da1-aab0-35cefbf506da
-- title:
--   Mpfx: ulp eq zpow of
-- statement:
--   The Mpfx construction uses the ulp eq zpow of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L32-L33
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L32-L33

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.ulp_eq_zpow_of (F : FiniteFormat) {x : ℝ} (h : ¬(x = 0 ∧ F.exp = ⊥)) :
    ulp F x = (2 : ℝ) ^ F.canonicalExp x := by sorry
