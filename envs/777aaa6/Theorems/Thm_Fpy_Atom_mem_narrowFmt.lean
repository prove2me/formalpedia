-- Prove2me | Theorems.Thm_Fpy_Atom_mem_narrowFmt
-- name    : Fpy.Atom.mem_narrowFmt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:14:01.730962+00:00
-- url     : https://prove2.me/theorems/192ebfa5-dd95-4478-80aa-ad94eab18ba8
-- title:
--   Atom: mem narrow Fmt
-- statement:
--   The Atom construction uses the mem narrow Fmt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L265-L271
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L265-L271

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}

theorem Fpy.Atom.mem_narrowFmt {a : Atom} {b : Bool} {F : Fmt} {u : Num} (hu : u ∈ F.γ)
    (ha : a.Holds u b) : u ∈ (a.narrowFmt b F).γ := by sorry
