-- Prove2me | Theorems.Thm_config_eff
-- name    : config_eff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:45:32.684809+00:00
-- url     : https://prove2.me/theorems/d1f99a31-375a-4bd4-bf32-6d13aa3a8f1b
-- title:
--   config eff: config eff
-- statement:
--   The divisor `toDiv d c` is effective if and only if $d \ge \deg(c)$, i.e. there are
--   enough chips at $q$ to cover any debt.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L232-L246
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L232-L246

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem config_eff {q : G.V} (d : ℤ) (c : Config G q) : effective (toDiv d c) ↔ d ≥ config_degree c := by sorry
