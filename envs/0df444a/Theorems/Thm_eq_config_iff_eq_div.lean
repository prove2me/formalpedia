-- Prove2me | Theorems.Thm_eq_config_iff_eq_div
-- name    : eq_config_iff_eq_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:31.629239+00:00
-- url     : https://prove2.me/theorems/59e422c8-00b0-4313-8723-7fff932e0bf3
-- title:
--   eq config iff eq div: eq config iff eq div
-- statement:
--   Two configurations are equal if and only if their images under `toDiv d` agree.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L73-L90
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L73-L90

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem eq_config_iff_eq_div {q : G.V} (d : ℤ) (c₁ c₂ : Config G q) : c₁ = c₂ ↔ toDiv d c₁ = toDiv d c₂ := by sorry
