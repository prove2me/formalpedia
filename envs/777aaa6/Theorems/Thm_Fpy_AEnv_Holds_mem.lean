-- Prove2me | Theorems.Thm_Fpy_AEnv_Holds_mem
-- name    : Fpy.AEnv.Holds.mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:31:51.696837+00:00
-- url     : https://prove2.me/theorems/d47958ad-5854-498a-8955-c5dbde564f37
-- title:
--   Holds: mem
-- statement:
--   If `fmt(yᵢ) ⊆ Fᵢ`, the value of each `yᵢ` lies in `Fᵢ`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L58-L66
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L58-L66

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}

theorem Fpy.AEnv.Holds.mem {Γ : AEnv D} {σ : Store} (hΓ : Γ.Holds σ) :
    ∀ {ys : List Var} {Fs : List D.Fmt} {ns : List Num}, FmtsIn Γ ys Fs →
      List.Forall₂ (fun y n => σ y = some (.num n)) ys ns →
      List.Forall₂ (fun n F => n ∈ D.γ F) ns Fs
  := by sorry
