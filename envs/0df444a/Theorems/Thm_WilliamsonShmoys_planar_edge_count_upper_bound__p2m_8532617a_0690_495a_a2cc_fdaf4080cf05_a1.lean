-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:38:41.561487+00:00
-- url     : https://prove2.me/theorems/3d5a3a76-5157-4153-9255-daafbf6c7150
-- title:
--   Euler upper bound for planar edge count
-- statement:
--   A finite simple graph with a planar drawing and at least three vertices has at most 3|V|−6 edges. This is the Euler edge bound; it can be proved by treating connected components, applying Euler's formula to a connected plane graph, and using that each face boundary has length at least three in a simple graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
