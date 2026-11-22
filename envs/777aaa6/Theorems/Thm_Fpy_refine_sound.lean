-- Prove2me | Theorems.Thm_Fpy_refine_sound
-- name    : Fpy.refine_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:14:15.718828+00:00
-- url     : https://prove2.me/theorems/b7eb2d6b-5c5a-4cf7-b1be-9fb8bbc1816d
-- title:
--   Fpy: refine sound
-- statement:
--   Refinement keeps every store that gives the test its outcome: the obligation
--   `Analysis.Sound.refine`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L323-L367
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L323-L367

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}
variable {c : Ceiling}

theorem Fpy.refine_sound {κ : Option Val} {C : Val} (hκ : Admits κ C) :
    ∀ (e : Expr (fpy decode)) {b : Bool} {Γ : AEnv (Fmt.domain c)} {σ : Store},
      Γ.Holds σ → Eval Φ σ C e (.bool b) → (refine κ e b Γ).Holds σ
  := by sorry
