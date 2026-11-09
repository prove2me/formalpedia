-- Prove2me | Theorems.Thm_WilliamsonShmoys_proper_supergraph_edge_ncard__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a2
-- name    : WilliamsonShmoys.proper_supergraph_edge_ncard__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T01:41:33.403068+00:00
-- url     : https://prove2.me/theorems/2429444a-1696-4ef3-8ffd-0941f5ad15c6
-- title:
--   Proper finite supergraphs increase edge-set cardinality
-- statement:
--   If one graph is a proper supergraph of another on the same finite vertex type, its edge set has strictly larger `ncard`. The parent uses this to turn maximal edge count into maximality under drawable extensions. Mathlib identifies graph inclusion with edge-set inclusion; graph inequality makes that inclusion proper, and finiteness of the vertex type makes both edge sets finite. The remaining core obligation is applying strict cardinal growth for a proper inclusion of finite sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.proper_supergraph_edge_ncard__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a2
    {V : Type}
    (H K : SimpleGraph V)
    (hHK : ∀ u v, H.Adj u v → K.Adj u v)
    (hne : H ≠ K) :
    H.edgeSet.ncard < K.edgeSet.ncard := by sorry
