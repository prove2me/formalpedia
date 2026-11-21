-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_subset_withBound_boundAfterNext
-- name    : Mpfx.FiniteFormat.subset_withBound_boundAfterNext
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:50:32.765011+00:00
-- url     : https://prove2.me/theorems/35429db8-732d-4f2e-ad65-6cf1646a7fdf
-- title:
--   Finite Format: subset with Bound bound After Next
-- statement:
--   `F ⊆ F.withBound next(b)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L544-L546
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L544-L546

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.FiniteFormat.subset_withBound_boundAfterNext (F : FiniteFormat) :
    F.toFormat ⊆ F.toFormat.withBound F.toFormat.boundAfterNext := by sorry
