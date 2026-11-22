-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_isEven_of_subset
-- name    : Mpfx.FiniteFormat.isEven_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:56.501491+00:00
-- url     : https://prove2.me/theorems/06578df3-73fc-4e71-a207-70742abe6320
-- title:
--   Finite Format: is Even of subset
-- statement:
--   **Values of a subformat's shrink are even.** If `y ∈ G ⊆ F` with
--   `F.p ≥ 2` and `y` in `G`'s shrink, then `y` is even in `F`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L309-L333
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L309-L333

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.isEven_of_subset {G : Format} {F : FiniteFormat} (hsub : G ⊆ F.toFormat)
    (hp : ((2 : ℕ) : Prec) ≤ F.p) {y : Dyadic} (hyG : y ∈ G)
    (hyC : y ∈ G.shrink.unbounded) : F.IsEven y := by sorry
