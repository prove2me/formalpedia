-- Prove2me | Theorems.Thm_burn_flow_reverse
-- name    : burn_flow_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:47:10.767967+00:00
-- url     : https://prove2.me/theorems/3f9503b6-dbd8-43e3-8871-8c187c73e8fa
-- title:
--   burn flow reverse: burn flow reverse
-- statement:
--   The `burn_flow` of a complete burn list is a valid orientation: for every edge
--   $\{u,v\}$, exactly `num_edges G u v` units of flow are directed in one of the two
--   directions.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L603-L623
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L603-L623

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem burn_flow_reverse {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (h_full : ∀ v : G.V, v ∈ L.list) : ∀ (u v : G.V), (burn_flow L ⟨u, v⟩) + (burn_flow L ⟨v, u⟩) = num_edges G u v := by sorry
