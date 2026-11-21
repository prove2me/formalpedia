-- Prove2me | Theorems.Thm_Mpfx_two_le_p_of_nontrivial
-- name    : Mpfx.two_le_p_of_nontrivial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:40:09.559261+00:00
-- url     : https://prove2.me/theorems/ecd50903-a154-490d-bcb5-3b23540d947a
-- title:
--   Mpfx: two le p of nontrivial
-- statement:
--   A nonzero member of `F₁` refutes the trivial branch of
--   `two_le_p_or_trivial_of_extend_one_withBound_subset`: the paper containment
--   then forces `2 ≤ F₂.p`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L644-L650
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L644-L650

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.two_le_p_of_nontrivial {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) : ((2 : ℕ) : Prec) ≤ F₂.p := by sorry
