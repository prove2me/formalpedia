-- Prove2me | Theorems.Thm_Fpy_Store_agree_updates
-- name    : Fpy.Store.agree_updates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:33:37.590206+00:00
-- url     : https://prove2.me/theorems/fc00c77c-d51e-4990-b934-59c95460514c
-- title:
--   Store: agree updates
-- statement:
--   The Store construction uses the agree updates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L91-L95
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L91-L95

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}

theorem Fpy.Store.agree_updates : ∀ (σ : Store) {ts : List Var} (vs : List Val),
    (∀ t ∈ ts, t ∈ X) → σ.Agree X (updates σ ts vs) := by sorry
