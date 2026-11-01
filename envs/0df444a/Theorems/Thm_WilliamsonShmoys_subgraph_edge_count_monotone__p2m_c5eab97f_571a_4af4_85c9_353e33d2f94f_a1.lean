-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edge_count_monotone__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
-- name    : WilliamsonShmoys.subgraph_edge_count_monotone__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:08.662186+00:00
-- url     : https://prove2.me/theorems/7615efd4-a911-4c0c-a14b-e114d77b083b
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, subgraph inclusion implies that the edge-set cardinality cannot decrease. This follows by inclusion of the finite edge sets and cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edge_count_monotone__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  sorry
