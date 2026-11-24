-- Prove2me | Theorems.Thm_gonality_geq_iff
-- name    : gonality_geq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:24.065986+00:00
-- url     : https://prove2.me/theorems/6a381018-b5eb-4464-942b-a73aced4ee18
-- title:
--   gonality geq iff: gonality geq iff
-- statement:
--   The relation `gonality_geq G k` is equivalent to the inequality `gonality h_conn ≥ k`.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L296-L318
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L296-L318

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset

theorem gonality_geq_iff {G : CFGraph} (h_conn : graph_connected G) (k : ℤ) :
    gonality_geq G k ↔ gonality h_conn ≥ k := by sorry
