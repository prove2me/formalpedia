-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulated_completion_exists
-- name    : WilliamsonShmoys.planar_triangulated_completion_exists
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:32:20.990016+00:00
-- url     : https://prove2.me/theorems/84c27a58-68e0-4d8d-9122-30e8c56f0976
-- title:
--   Every finite simple planar graph has a triangulated planar completion
-- statement:
--   For every finite simple graph with at least three vertices and a crossing-free drawing as defined by HasPlanarDrawingOn, there is a planar supergraph on the same vertex type whose faces are triangles and whose edge count is exactly three times the number of vertices minus six. One proof route joins drawing components, adds noncrossing diagonals until all faces are triangular, then applies Euler’s formula and counts face-edge incidences. The vertex-count hypothesis is retained for the triangulation count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulated_completion_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
