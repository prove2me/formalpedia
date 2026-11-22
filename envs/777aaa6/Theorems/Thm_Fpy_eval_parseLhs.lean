-- Prove2me | Theorems.Thm_Fpy_eval_parseLhs
-- name    : Fpy.eval_parseLhs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:48.939401+00:00
-- url     : https://prove2.me/theorems/35ded3a0-975a-48cd-bb62-7654ebbfb926
-- title:
--   Fpy: eval parse Lhs
-- statement:
--   The Fpy construction uses the eval parse Lhs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L87-L120
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L87-L120

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}

theorem Fpy.eval_parseLhs {κ : Option Val} {e : Expr (fpy decode)} {x : Var} {g : Lhs}
    (he : parseLhs κ e = some (x, g)) {σ : Store} {C : Val} (hκ : Admits κ C) {n : Num}
    (h : Eval Φ σ C e (.num n)) : ∃ u, σ x = some (.num u) ∧ n = g.eval u := by sorry
