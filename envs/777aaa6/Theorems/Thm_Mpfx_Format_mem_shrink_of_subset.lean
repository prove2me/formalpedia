-- Prove2me | Theorems.Thm_Mpfx_Format_mem_shrink_of_subset
-- name    : Mpfx.Format.mem_shrink_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:54:52.062055+00:00
-- url     : https://prove2.me/theorems/a0495f3f-ef5f-4c71-bb3a-03e7e3f543a4
-- title:
--   Format: mem shrink of subset
-- statement:
--   **Shrinking is monotone.** If `G ⊆ H`, with `G`'s bound one of its values
--   and `G` nontrivial, then `G`'s shrink lies in `H`'s once `H.p ≥ 2`. Both
--   containment rules survive the shift `(p − 1, exp + 1)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L651-L662
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L651-L662

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.mem_shrink_of_subset {G H : Format} (hsub : G ⊆ H) (hbr : BoundRep G)
    (hnt : G.Nontrivial) (hp : ((2 : ℕ) : Prec) ≤ H.p) {y : Dyadic} (hy : y ∈ G.shrink) :
    y ∈ H.shrink.unbounded := by sorry
