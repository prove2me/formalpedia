-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion_06232b3e
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_06232b3e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:04:55.894396+00:00
-- url     : https://prove2.me/theorems/638a1f84-48cf-416d-8d32-57bed5d6bb46
-- title:
--   A drawable graph has an exact edge-count completion
-- statement:
--   Every drawable finite simple graph on at least three vertices can be extended, on the same vertex type, to a drawable graph with exactly 3|V|−6 edges. For three vertices the completion is the triangle; for larger vertex sets, the route is to extend to a maximal drawable graph, establish that its drawing is triangulated, and count using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_06232b3e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
