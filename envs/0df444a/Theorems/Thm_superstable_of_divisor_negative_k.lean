-- Prove2me | Theorems.Thm_superstable_of_divisor_negative_k
-- name    : superstable_of_divisor_negative_k
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:12.423868+00:00
-- url     : https://prove2.me/theorems/d4cc5539-8cc8-4f2f-a56b-8cb63f4c3090
-- title:
--   superstable of divisor negative k: superstable of divisor negative k
-- statement:
--   If $D$ is unwinnable and $D \sim c + k \cdot q$ for a superstable $c$, then $k < 0$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L69-L84
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L69-L84

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem superstable_of_divisor_negative_k (G : CFGraph) (q : G.V) (D : CFDiv G) :
  ¬(winnable G D) →
  ∀ (c : Config G q) (k : ℤ),
    linear_equiv G D (c.chips + k • (one_chip q)) →
    superstable G q c →
    k < 0 := by sorry
