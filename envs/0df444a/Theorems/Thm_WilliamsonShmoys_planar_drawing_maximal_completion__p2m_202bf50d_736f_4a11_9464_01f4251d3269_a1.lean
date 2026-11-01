-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_completion__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_completion__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:20.53957+00:00
-- url     : https://prove2.me/theorems/a34ee183-b91b-4a67-873f-251f94ba9522
-- title:
--   Maximal drawable completion
-- statement:
--   Every drawable graph on the given finite vertex set has a drawable supergraph that is maximal under edge inclusion among drawable simple graphs on that same set; the original edge count is at most the completion’s edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_completion__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeFinset.card ≤ H.edgeSet.ncard ∧
      (∀ J : SimpleGraph V,
        H.edgeSet ⊆ J.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn J →
        J.edgeSet ⊆ H.edgeSet) := by sorry
