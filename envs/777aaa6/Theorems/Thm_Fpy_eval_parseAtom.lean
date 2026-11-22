-- Prove2me | Theorems.Thm_Fpy_eval_parseAtom
-- name    : Fpy.eval_parseAtom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:43.393179+00:00
-- url     : https://prove2.me/theorems/4e06b5cf-377f-4445-b48b-4bf2170e8eeb
-- title:
--   Fpy: eval parse Atom
-- statement:
--   The Fpy construction uses the eval parse Atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L138-L157
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L138-L157

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}

theorem Fpy.eval_parseAtom {κ : Option Val} {e : Expr (fpy decode)} {a : Atom}
    (he : parseAtom κ e = some a) {σ : Store} {C : Val} (hκ : Admits κ C) {b : Bool}
    (h : Eval Φ σ C e (.bool b)) : ∃ u, σ a.x = some (.num u) ∧ a.Holds u b := by sorry
