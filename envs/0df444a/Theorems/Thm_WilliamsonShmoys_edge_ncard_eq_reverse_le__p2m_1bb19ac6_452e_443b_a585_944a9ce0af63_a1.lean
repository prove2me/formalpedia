-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_eq_reverse_le__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
-- name    : WilliamsonShmoys.edge_ncard_eq_reverse_le__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:02.882779+00:00
-- url     : https://prove2.me/theorems/7b5bf920-ce90-4ad6-a32b-47a4a5227147
-- title:
--   Equal edge counts force reverse graph inclusion
-- statement:
--   For graphs on a finite vertex type, subgraph inclusion and equal edge-set cardinalities imply reverse inclusion. Prove by finite-set extensionality and the fact that a finite subset with the same cardinality as its superset is equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_ncard_eq_reverse_le__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hcard : G.edgeSet.ncard = H.edgeSet.ncard) :
    H ≤ G := by sorry
