-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_count_of_drawing
-- name    : WilliamsonShmoys.exists_planar_supergraph_edge_count_of_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:29:50.629801+00:00
-- url     : https://prove2.me/theorems/12c87c45-1adf-4e39-a6f7-9fa160e558d3
-- title:
--   Planar supergraph with the maximal planar edge count
-- statement:
--   Every finite simple graph with the specified crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set with exactly 3n−6 edges. For n=3, the extension is the triangle; for larger n, a concrete proof route is to extend the embedding to a triangulation and apply Euler’s formula. This removes the geometric augmentation and edge-count work from the parent. The remaining core obligation is to formalize the triangulation extension, including disconnected drawings, for the exact arc-based `HasPlanarDrawingOn` predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_planar_supergraph_edge_count_of_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
