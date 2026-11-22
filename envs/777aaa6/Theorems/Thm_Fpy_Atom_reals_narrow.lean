-- Prove2me | Theorems.Thm_Fpy_Atom_reals_narrow
-- name    : Fpy.Atom.reals_narrow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:52.461024+00:00
-- url     : https://prove2.me/theorems/929f6b36-bc33-4b45-98fc-7d51d4caaeac
-- title:
--   Atom: reals narrow
-- statement:
--   The Atom construction uses the reals narrow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L212-L256
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L212-L256

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}

theorem Fpy.Atom.reals_narrow {a : Atom} {b : Bool} {F : Format} {u : Num} (hu : u ∈ F.reals)
    (ha : a.Holds u b) : u ∈ (a.narrow b F).reals := by sorry
