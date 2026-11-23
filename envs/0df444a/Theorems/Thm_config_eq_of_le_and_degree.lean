-- Prove2me | Theorems.Thm_config_eq_of_le_and_degree
-- name    : config_eq_of_le_and_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:47:02.865338+00:00
-- url     : https://prove2.me/theorems/15e960b4-da35-4919-995a-40b12e730234
-- title:
--   config eq of le and degree: config eq of le and degree
-- statement:
--   Two configurations are equal if one is pointwise bounded above by the other and they have
--   the same degree.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L271-L295
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L271-L295

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem config_eq_of_le_and_degree {q : G.V} {c1 c2 : Config G q} (h_le : c2 ≤ c1)
    (h_deg : config_degree c1 = config_degree c2) : c1 = c2 := by sorry
