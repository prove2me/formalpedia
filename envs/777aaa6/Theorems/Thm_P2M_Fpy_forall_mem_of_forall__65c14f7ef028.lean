-- Prove2me | Theorems.Thm_P2M_Fpy_forall_mem_of_forall__65c14f7ef028
-- name    : P2M_Fpy_forall_mem_of_forall__65c14f7ef028
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:38:05.663596+00:00
-- url     : https://prove2.me/theorems/6b4f7355-e378-4805-8193-a146a6a7640b
-- title:
--   P2 M Fpy forall mem of forall  65c14f7ef028: P2 M Fpy forall mem of forall  65c14f7ef028
-- statement:
--   Inputs in `Fᵢ ⊆ S` lie in `S`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L247-L253
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L247-L253

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}

theorem P2M_Fpy_forall_mem_of_forall__65c14f7ef028 {S : Set Num} :
    ∀ {us : List Num} {Fs : List D.Fmt}, List.Forall₂ (fun u F => u ∈ D.γ F) us Fs →
      (∀ F ∈ Fs, D.γ F ⊆ S) → ∀ u ∈ us, u ∈ S
  := by sorry

alias «Fpy».«forall_mem_of_forall₂» := P2M_Fpy_forall_mem_of_forall__65c14f7ef028
