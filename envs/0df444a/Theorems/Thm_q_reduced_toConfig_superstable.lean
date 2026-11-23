-- Prove2me | Theorems.Thm_q_reduced_toConfig_superstable
-- name    : q_reduced_toConfig_superstable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:45:18.928252+00:00
-- url     : https://prove2.me/theorems/6ca848e1-c003-49a9-8cba-a0e91aa7bc16
-- title:
--   q reduced to Config superstable: q reduced to Config superstable
-- statement:
--   The canonical configuration of a $q$-reduced divisor is superstable.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L351-L355
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L351-L355

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem q_reduced_toConfig_superstable (G : CFGraph) (q : G.V) (D : CFDiv G)
    (h_qred : q_reduced G q D) :
    superstable G q (toConfig ⟨D, h_qred.1⟩) := by sorry
