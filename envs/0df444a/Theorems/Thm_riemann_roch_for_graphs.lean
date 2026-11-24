-- Prove2me | Theorems.Thm_riemann_roch_for_graphs
-- name    : riemann_roch_for_graphs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:35.782041+00:00
-- url     : https://prove2.me/theorems/8384bd25-c08c-4527-a1b5-6a7035da012a
-- title:
--   riemann roch for graphs: riemann roch for graphs
-- statement:
--   **Riemann-Roch theorem for graphs:** $r(D) - r(K_G - D) = \deg(D) + 1 - g$.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 5.9.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L24-L33
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L24-L33

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset

theorem riemann_roch_for_graphs {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  rank G D - rank G (canonical_divisor G - D) = deg D - genus G + 1 := by sorry
