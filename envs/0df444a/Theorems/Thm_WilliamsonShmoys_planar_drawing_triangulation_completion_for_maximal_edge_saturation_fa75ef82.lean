-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_for_maximal_edge_saturation_fa75ef82
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_for_maximal_edge_saturation_fa75ef82
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:49:18.901381+00:00
-- url     : https://prove2.me/theorems/e8ae6a5a-5a4c-4f53-9707-6853e31c2747
-- title:
--   Triangulation completion for maximal edge saturation
-- statement:
--   A finite graph with a crossing-free drawing and at least three vertices extends on the same vertex type to a drawable triangulation with edge count exactly three times the vertex count minus six. The three-vertex boundary is included; disconnected drawings require a valid component-joining step in the proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_for_maximal_edge_saturation_fa75ef82
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
