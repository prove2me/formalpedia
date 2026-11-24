-- Prove2me | Theorems.Thm_superstable_of_divisor
-- name    : superstable_of_divisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:03.762033+00:00
-- url     : https://prove2.me/theorems/33b27441-8ec3-47c0-8fb3-71ad0bc2d632
-- title:
--   superstable of divisor: superstable of divisor
-- statement:
--   Every divisor $D$ is linearly equivalent to $c+kq$ for some superstable configuration
--   $c$ and integer $k$.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Remark 3.14.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L53-L66
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L53-L66

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem superstable_of_divisor {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃ (c : Config G q) (k : ℤ),
    linear_equiv G D (c.chips + k • (one_chip q)) ∧
    superstable G q c := by sorry
