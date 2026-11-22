-- Prove2me | Theorems.Thm_Fpy_reals_finite
-- name    : Fpy.reals_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:31:53.232512+00:00
-- url     : https://prove2.me/theorems/c958d7a9-8c6a-4cfd-9aea-fe1622c635d8
-- title:
--   Fpy: reals finite
-- statement:
--   The Fpy construction uses the reals finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L305-L310
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L305-L310

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
variable {decode : List (Label × Val) → Option RoundCtx}

theorem Fpy.reals_finite {F : Format} {u : Num} {a : ℝ} (hu : u ∈ F.reals) (h : u = .finite a) :
    ∃ d ∈ F, (d : ℝ) = a := by sorry
