-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_mono__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
-- name    : WilliamsonShmoys.edge_ncard_mono__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:00.762311+00:00
-- url     : https://prove2.me/theorems/da95c49e-1e1c-4c71-945a-e9f473259652
-- title:
--   Edge cardinality is monotone under graph inclusion
-- statement:
--   If G is a subgraph of H on a finite vertex type, then G's finite edge set has cardinality at most H's. This supplies the cardinality inequality needed when comparing a candidate maximum with a drawable extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_ncard_mono__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
