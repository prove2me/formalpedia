-- Prove2me | Theorems.Thm_WilliamsonShmoys_proper_supergraph_edge_ncard__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
-- name    : WilliamsonShmoys.proper_supergraph_edge_ncard__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:01:09.04031+00:00
-- url     : https://prove2.me/theorems/d9db2ec7-5103-4595-bcef-90b1b630e56b
-- title:
--   Proper finite supergraphs have more edges
-- statement:
--   This converts maximality of edge count into maximality under graph extension. The pairwise adjacency hypothesis gives inclusion of edge sets, and graph inequality makes that inclusion proper. Because V is finite, both edge sets are finite, so proper inclusion strictly increases ncard. This removes the strict-growth argument from the parent. An independent proof route is to establish edge-set inclusion and properness, then apply strict cardinality growth for a proper inclusion of finite sets. The [Fintype V] hypothesis is essential to this route and is now explicit.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.proper_supergraph_edge_ncard__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : ∀ u v, H.Adj u v → K.Adj u v)
    (hne : H ≠ K) :
    H.edgeSet.ncard < K.edgeSet.ncard := by sorry
