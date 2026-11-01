-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_to_triangulation__p2m_0448f4f3_6535_4d82_8dda_cbfbd113fe3f_a2
-- name    : WilliamsonShmoys.planar_drawing_augmentation_to_triangulation__p2m_0448f4f3_6535_4d82_8dda_cbfbd113fe3f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:58:25.927533+00:00
-- url     : https://prove2.me/theorems/2d721275-eabe-421b-ae9b-fc6b7bdcfafc
-- title:
--   Triangulated drawable supergraph completion
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation_to_triangulation__p2m_0448f4f3_6535_4d82_8dda_cbfbd113fe3f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
