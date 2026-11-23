-- Prove2me | Theorems.Thm_q_reduced_eq_chips_add_q
-- name    : q_reduced_eq_chips_add_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:45:33.106332+00:00
-- url     : https://prove2.me/theorems/86242d27-fdde-4a02-ab50-47dd70874243
-- title:
--   q reduced eq chips add q: q reduced eq chips add q
-- statement:
--   A $q$-reduced divisor is its canonical configuration plus its chips at $q$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L195-L205
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L195-L205

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem q_reduced_eq_chips_add_q (G : CFGraph) (q : G.V) (D : CFDiv G)
    (h_qred : q_reduced G q D) :
    D = (toConfig ⟨D, h_qred.1⟩).chips + D q • one_chip q := by sorry
