-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension__p2m_8c9864f5_741a_481d_8578_325697296ee9_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_8c9864f5_741a_481d_8578_325697296ee9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:33:26.469198+00:00
-- url     : https://prove2.me/theorems/34c1d13a-c463-44f3-a4ff-eb6476f05c93
-- title:
--   Extend a finite planar drawing to a triangulated graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type whose edge count is three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_8c9864f5_741a_481d_8578_325697296ee9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V, G ≤ T ∧ HasPlanarDrawingOn T ∧
      (letI : DecidableRel T.Adj := Classical.decRel T.Adj
       T.edgeFinset.card = 3 * Fintype.card V - 6) := by
  sorry
