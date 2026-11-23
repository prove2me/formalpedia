-- Prove2me | Theorems.Thm_q_reduced_eq_chips_sub_one_chip
-- name    : q_reduced_eq_chips_sub_one_chip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:21.243296+00:00
-- url     : https://prove2.me/theorems/fa66920b-8a36-43bd-b899-d4a855cc58df
-- title:
--   q reduced eq chips sub one chip: q reduced eq chips sub one chip
-- statement:
--   If a $q$-reduced divisor has value $-1$ at $q$, it is exactly $c-q$ for its
--   canonical configuration $c$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L209-L217
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L209-L217

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem q_reduced_eq_chips_sub_one_chip (G : CFGraph) (q : G.V) (D : CFDiv G)
    (h_qred : q_reduced G q D) (h_q : D q = -1) :
    D = (toConfig ⟨D, h_qred.1⟩).chips - one_chip q := by sorry
