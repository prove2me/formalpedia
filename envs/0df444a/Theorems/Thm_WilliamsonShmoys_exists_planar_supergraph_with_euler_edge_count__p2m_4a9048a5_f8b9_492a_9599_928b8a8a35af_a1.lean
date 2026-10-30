-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_euler_edge_count__p2m_4a9048a5_f8b9_492a_9599_928b8a8a35af_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_euler_edge_count__p2m_4a9048a5_f8b9_492a_9599_928b8a8a35af_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:35:43.181427+00:00
-- url     : https://prove2.me/theorems/7cbf1ba0-37d6-4547-8de0-56512f488909
-- title:
--   Planar augmentation to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three fixed vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_with_euler_edge_count__p2m_4a9048a5_f8b9_492a_9599_928b8a8a35af_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry
