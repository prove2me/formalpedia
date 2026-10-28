-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_supergraph_triangulation_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_supergraph_triangulation_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:01:35.420601+00:00
-- url     : https://prove2.me/theorems/95ea5390-fb6e-4fba-bf69-47c1f73748f3
-- title:
--   A planar drawing extends to a triangulated supergraph
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertices with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_supergraph_triangulation_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
