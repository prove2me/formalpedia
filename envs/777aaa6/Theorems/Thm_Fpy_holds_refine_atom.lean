-- Prove2me | Theorems.Thm_Fpy_holds_refine_atom
-- name    : Fpy.holds_refine_atom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:14:05.72387+00:00
-- url     : https://prove2.me/theorems/da93bce7-9679-483d-9efc-e1c09e0e3dd1
-- title:
--   Fpy: holds refine atom
-- statement:
--   The Fpy construction uses the holds refine atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L312-L319
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L312-L319

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}
variable {c : Ceiling}

theorem Fpy.holds_refine_atom {κ : Option Val} {e : Expr (fpy decode)} {b : Bool}
    {Γ : AEnv (Fmt.domain c)} {σ : Store} {C : Val} (hΓ : Γ.Holds σ) (hκ : Admits κ C)
    (h : Eval Φ σ C e (.bool b)) : ((parseAtom κ e).elim Γ (·.refine b Γ)).Holds σ := by sorry
