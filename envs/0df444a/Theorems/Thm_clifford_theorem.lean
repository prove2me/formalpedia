-- Prove2me | Theorems.Thm_clifford_theorem
-- name    : clifford_theorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:02.505281+00:00
-- url     : https://prove2.me/theorems/bcc60cb8-9e3a-4994-b0e2-03eb6d09fbb4
-- title:
--   clifford theorem: clifford theorem
-- statement:
--   **Clifford's theorem:** If $r(D) \geq 0$ and $r(K_G - D) \geq 0$, then
--   $r(D) \leq \frac12 \deg(D)$.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 5.13.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L131-L171
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L131-L171

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset

theorem clifford_theorem
    {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G)
    (h_D : rank G D ≥ 0)
    (h_KD : rank G (canonical_divisor G - D) ≥ 0) :
    (rank G D : ℚ) ≤ (deg D : ℚ) / 2 := by sorry
