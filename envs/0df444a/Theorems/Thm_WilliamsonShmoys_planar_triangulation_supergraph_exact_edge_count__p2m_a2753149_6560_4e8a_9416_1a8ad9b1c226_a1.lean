-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_a2753149_6560_4e8a_9416_1a8ad9b1c226_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_a2753149_6560_4e8a_9416_1a8ad9b1c226_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:19:46.903659+00:00
-- url     : https://prove2.me/theorems/718d0665-f14e-4e4a-9ebf-3d91778b5251
-- title:
--   Exact edge count for a drawable planar completion
-- statement:
--   Every drawable finite simple graph on at least three vertices extends, without adding vertices, to a drawable supergraph with exactly 3|V|−6 edges. The extension can be obtained by adding noncrossing edges until the embedding is maximal, then proving its faces are triangles and counting edges via Euler’s formula. For three vertices the triangle is the maximal completion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_a2753149_6560_4e8a_9416_1a8ad9b1c226_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 = N.edgeSet.ncard := by sorry
