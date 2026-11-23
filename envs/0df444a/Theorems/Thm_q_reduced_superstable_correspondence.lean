-- Prove2me | Theorems.Thm_q_reduced_superstable_correspondence
-- name    : q_reduced_superstable_correspondence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:45:40.757798+00:00
-- url     : https://prove2.me/theorems/2f0246d6-1ebe-487e-9cda-52e491bc228f
-- title:
--   q reduced superstable correspondence: q reduced superstable correspondence
-- statement:
--   A divisor is $q$-reduced if and only if it corresponds to a superstable configuration with
--     respect to $q$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L359-L372
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L359-L372

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem q_reduced_superstable_correspondence (G : CFGraph) (q : G.V) (D : CFDiv G) :
  q_reduced G q D ↔ ∃ c : Config G q, superstable G q c ∧
  D = toDiv (deg D) c := by sorry
