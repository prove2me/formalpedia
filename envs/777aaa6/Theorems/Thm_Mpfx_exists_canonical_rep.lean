-- Prove2me | Theorems.Thm_Mpfx_exists_canonical_rep
-- name    : Mpfx.exists_canonical_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:39:39.537894+00:00
-- url     : https://prove2.me/theorems/45d0bf5d-3f68-49f9-8151-41c299a39ac5
-- title:
--   Mpfx: exists canonical rep
-- statement:
--   **Canonical representation.** A positive `y ∈ F` (precision `p`) is
--   `c · 2^(canonicalExp y)` with `|c| < 2^p` (Flocq `canonical_generic_format`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Discrete.lean#L33-L39
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Discrete.lean#L33-L39

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Discrete
set_option autoImplicit true
open Mpfx

theorem Mpfx.exists_canonical_rep (F : FiniteFormat) {p : ℕ}
    (hp : F.p = (p : Prec))
    {y : _root_.Mpfx.Dyadic} (hmem : y ∈ F) (hpos : 0 < (y : ℝ)) :
    ∃ c : ℤ, |c| < (2 : ℤ) ^ p ∧
      (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ (F.canonicalExp (y : ℝ)) := by sorry
