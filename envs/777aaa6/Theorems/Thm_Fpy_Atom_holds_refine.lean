-- Prove2me | Theorems.Thm_Fpy_Atom_holds_refine
-- name    : Fpy.Atom.holds_refine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:14:13.551957+00:00
-- url     : https://prove2.me/theorems/f1e9d6b5-b8ab-47b1-8bbc-d7faeee1a60e
-- title:
--   Atom: holds refine
-- statement:
--   The Atom construction uses the holds refine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L284-L297
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L284-L297

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}
variable {c : Ceiling}

theorem Fpy.Atom.holds_refine {a : Atom} {b : Bool} {Γ : AEnv (Fmt.domain c)} {σ : Store}
    (hΓ : Γ.Holds σ) {u : Num} (hx : σ a.x = some (.num u)) (ha : a.Holds u b) :
    (a.refine b Γ).Holds σ := by sorry
