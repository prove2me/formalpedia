-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_augmentation__p2m_ac724374_f88c_4ddf_bad5_42fda9b092d4_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_augmentation__p2m_ac724374_f88c_4ddf_bad5_42fda9b092d4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:42:29.497604+00:00
-- url     : https://prove2.me/theorems/7021208f-8613-4620-af29-8109890d733a
-- title:
--   Augmenting a sparse planar drawing
-- statement:
--   For a drawable simple graph on at least three vertices, if its edge count is strictly below the planar triangulation bound, there is a strict drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_augmentation__p2m_ac724374_f88c_4ddf_bad5_42fda9b092d4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel S.Adj := Classical.decRel S.Adj
    S.edgeFinset.card + 6 < 3 * Fintype.card V →
      ∃ T : SimpleGraph V,
        S ≤ T ∧ T ≠ S ∧ WilliamsonShmoys.HasPlanarDrawingOn T := by sorry
