-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_mono_of_subgraph__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
-- name    : WilliamsonShmoys.edge_card_mono_of_subgraph__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:16:01.903507+00:00
-- url     : https://prove2.me/theorems/667edf1f-a15f-4894-a812-e29f8b1520f9
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, inclusion of adjacency relations implies inclusion of edge sets and hence monotonicity of edge count. This is the elementary transfer step that returns the connected supergraph’s bound to H. Prove by showing every edge of H is an edge of K, then applying finite-set cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_card_mono_of_subgraph__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    H.edgeFinset.card ≤ K.edgeFinset.card := by sorry
