-- Prove2me | Theorems.Thm_rank_nonspecial_range
-- name    : rank_nonspecial_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:59.94579+00:00
-- url     : https://prove2.me/theorems/83dab25b-0371-429b-99fc-9312d0ecab09
-- title:
--   rank nonspecial range: rank nonspecial range
-- statement:
--   The rank of a divisor in terms of its degree:
--     - $\deg(D) < 0 \Rightarrow r(D) = -1$
--     - $0 \leq \deg(D) \leq 2g-2 \Rightarrow r(D) \leq \deg(D)/2$
--     - $\deg(D) > 2g-2 \Rightarrow r(D) = \deg(D) - g$.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 5.14.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L179-L224
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L179-L224

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset

theorem rank_nonspecial_range
  {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  -- Part 1
  (deg D < 0 → rank G D = -1) ∧
  -- Part 2
  (0 ≤ (deg D : ℚ) ∧ (deg D : ℚ) ≤ 2 * (genus G : ℚ) - 2 → (rank G D : ℚ) ≤ (deg D : ℚ) / 2) ∧
  -- Part 3
  (deg D > 2 * genus G - 2 → rank G D = deg D - genus G) := by sorry
