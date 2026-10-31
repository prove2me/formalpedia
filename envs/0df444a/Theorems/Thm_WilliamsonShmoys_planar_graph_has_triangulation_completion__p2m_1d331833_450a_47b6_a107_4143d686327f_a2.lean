-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_completion__p2m_1d331833_450a_47b6_a107_4143d686327f_a2
-- name    : WilliamsonShmoys.planar_graph_has_triangulation_completion__p2m_1d331833_450a_47b6_a107_4143d686327f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:19:30.881361+00:00
-- url     : https://prove2.me/theorems/39622fc7-9624-4f8c-802c-be6d654a55c6
-- title:
--   Every finite drawable graph has a triangulation completion
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable simple graph on the same vertex set whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulation_completion__p2m_1d331833_450a_47b6_a107_4143d686327f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G <= H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
