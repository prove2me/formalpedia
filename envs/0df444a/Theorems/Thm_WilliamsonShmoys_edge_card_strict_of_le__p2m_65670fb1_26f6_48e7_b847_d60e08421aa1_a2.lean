-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_strict_of_le__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
-- name    : WilliamsonShmoys.edge_card_strict_of_le__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:57:10.855041+00:00
-- url     : https://prove2.me/theorems/1f7e52fc-6782-4f23-b26a-08cd4b634c5b
-- title:
--   Strict graph extension increases finite edge count
-- statement:
--   For simple graphs on a finite vertex type, a proper extension has strictly more edges. This follows by viewing the edge sets as finite sets and applying strict monotonicity of finite cardinality under proper inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_card_strict_of_le__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hne : H ≠ K) :
    H.edgeSet.ncard < K.edgeSet.ncard := by sorry
