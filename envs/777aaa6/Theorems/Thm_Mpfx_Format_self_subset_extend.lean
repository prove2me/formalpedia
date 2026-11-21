-- Prove2me | Theorems.Thm_Mpfx_Format_self_subset_extend
-- name    : Mpfx.Format.self_subset_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:38:51.039437+00:00
-- url     : https://prove2.me/theorems/fbb3370c-4a2a-4e0a-971f-4e78681d86a6
-- title:
--   Format: self subset extend
-- statement:
--   `F ⊆ F.extend k`: extending only relaxes the precision and quantum
--   constraints.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L438-L448
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L438-L448

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.self_subset_extend (F : Format) (k : ℕ) : F ⊆ F.extend k := by sorry
