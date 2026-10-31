-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count__p2m_1cec101a_a7da_4edb_96e9_a9cac5943fca_a1
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_1cec101a_a7da_4edb_96e9_a9cac5943fca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:48:47.738737+00:00
-- url     : https://prove2.me/theorems/db367b77-db98-427b-b1c6-513aa1e72eeb
-- title:
--   Planar supergraph triangulation edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|-6 edges. The extension is obtained by adding drawable edges until the embedding is triangulated; Euler's formula then gives the edge count. In the parent proof, maximality forces this extension to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_1cec101a_a7da_4edb_96e9_a9cac5943fca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V) :
    exists P : SimpleGraph V, N <= P /\ HasPlanarDrawingOn P /\
      P.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
