-- Prove2me | Theorems.Thm_burn_flow_directed
-- name    : burn_flow_directed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:48.244067+00:00
-- url     : https://prove2.me/theorems/eb170678-e81b-4a62-a634-a783fa223597
-- title:
--   burn flow directed: burn flow directed
-- statement:
--   The `burn_flow` of a complete burn list is directed: for every pair $(u,v)$, flow goes
--   in at most one direction.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L627-L644
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L627-L644

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem burn_flow_directed {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (h_full : ∀ v : G.V, v ∈ L.list) : ∀ (u v : G.V), burn_flow L ⟨u,v⟩ = 0 ∨ burn_flow L ⟨v,u⟩ = 0 := by sorry
