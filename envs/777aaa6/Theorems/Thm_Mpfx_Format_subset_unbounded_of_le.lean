-- Prove2me | Theorems.Thm_Mpfx_Format_subset_unbounded_of_le
-- name    : Mpfx.Format.subset_unbounded_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:54:04.160926+00:00
-- url     : https://prove2.me/theorems/5107ec44-f5f9-4f0a-9ac5-fff3013f5dea
-- title:
--   Format: subset unbounded of le
-- statement:
--   **Containment into an unbounded format.** Since `F.unbounded.b = ⊤` accepts
--   every magnitude, `𝒜-Contains-Prec` (`containsPrec`) reduces to the precision and
--   quantum orderings alone: a format with precision at most `F.p` and quantum at
--   least `F.exp` is contained in `F.unbounded`. This is the shared "the exact result
--   is representable in the wide format" step behind every operation-specific
--   double-rounding rule (§5.2).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L79-L82
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L79-L82

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.subset_unbounded_of_le {F G : Format}
    (hp : G.p ≤ F.p) (he : F.exp ≤ G.exp) (hs : G.specials ⊆ F.specials) :
    G ⊆ F.unbounded := by sorry
