-- Prove2me | Theorems.Thm_burnin_degree
-- name    : burnin_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:47:19.529615+00:00
-- url     : https://prove2.me/theorems/9a53503f-797d-4ba1-8857-bda94b6dc27d
-- title:
--   burnin degree: burnin degree
-- statement:
--   For any vertex $v \ne q$ in a burn list, the in-flow into $v$ exceeds the number of
--   chips at $v$. This is the key inequality used to construct an acyclic orientation from a
--   superstable configuration.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L649-L773
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L649-L773

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem burnin_degree {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (v : G.V) (h_pres : v ∈ L.list) (h_ne : v ≠ q): ∑ (w : G.V), burn_flow L ⟨w,v⟩ > c.chips v := by sorry
