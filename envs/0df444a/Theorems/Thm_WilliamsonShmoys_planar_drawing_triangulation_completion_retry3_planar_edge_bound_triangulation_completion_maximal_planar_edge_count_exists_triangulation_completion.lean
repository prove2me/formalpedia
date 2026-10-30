-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count_exists_triangulation_completion
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count_exists_triangulation_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:34:58.104762+00:00
-- url     : https://prove2.me/theorems/e61f28a9-1cfe-4034-b8f5-465588f1e501
-- title:
--   Completion of a drawable graph to a triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable graph on the same vertex type with exactly 3|V|−6 edges. For three vertices the completion is the triangle; in general the proof extends to a maximal drawable supergraph, shows its faces are triangular, and applies Euler’s formula. This is the geometric completion obligation used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count_exists_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V, T ≤ U ∧ HasPlanarDrawingOn U ∧
      U.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
