-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion_edge_count
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_completion_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:12:30.283772+00:00
-- url     : https://prove2.me/theorems/4e62805d-6ee4-4d9f-8a75-ab9e7a5d6a37
-- title:
--   Planar drawing has a maximal edge-count completion
-- statement:
--   Every simple graph with a crossing-free drawing on at least three fixed vertices is contained in a crossing-free graph on those same vertices with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulated_completion_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      M.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
