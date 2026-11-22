-- Prove2me | Theorems.Thm_Fpy_reals_fmtJoin_of_eq_or
-- name    : Fpy.reals_fmtJoin_of_eq_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:23.367628+00:00
-- url     : https://prove2.me/theorems/a91391ca-86b7-41f0-a244-f0dad83d8a35
-- title:
--   Fpy: reals fmt Join of eq or
-- statement:
--   The Fpy construction uses the reals fmt Join of eq or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L302-L306
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L302-L306

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.reals_fmtJoin_of_eq_or {F₁ F₂ : Format} {u v n : Num} (hu : u ∈ F₁.reals)
    (hv : v ∈ F₂.reals) (h : n = u ∨ n = v) : n ∈ (fmtJoin F₁ F₂).reals := by sorry
