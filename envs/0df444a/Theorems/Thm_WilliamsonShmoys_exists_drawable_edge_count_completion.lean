-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_count_completion
-- name    : WilliamsonShmoys.exists_drawable_edge_count_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:51:37.755743+00:00
-- url     : https://prove2.me/theorems/91679e32-5c82-4cc7-b5b1-dcdad4dff49f
-- title:
--   Drawable graph has an exact edge-count completion
-- statement:
--   Every finite drawable simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly `3 * |V| - 6` edges. At three vertices the completion is the triangle; for larger vertex sets, add drawable edges until the embedding is maximal, then count its triangular faces using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
