-- Prove2me | Theorems.Thm_Fpy_Num_div_eq_finite
-- name    : Fpy.Num.div_eq_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:06:30.553165+00:00
-- url     : https://prove2.me/theorems/fbbcd2c7-50ea-4907-818c-53e0df26d0ae
-- title:
--   Num: div eq finite
-- statement:
--   The Num construction uses the div eq finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L132-L139
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L132-L139

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.Num.div_eq_finite {u v : Num} {x : ℝ} (h : Num.div u v = .finite x) :
    (∃ a b, u = .finite a ∧ v = .finite b ∧ b ≠ 0 ∧ x = a / b) ∨
      (∃ a s, u = .finite a ∧ v = .special (.inf s) ∧ x = 0) := by sorry
