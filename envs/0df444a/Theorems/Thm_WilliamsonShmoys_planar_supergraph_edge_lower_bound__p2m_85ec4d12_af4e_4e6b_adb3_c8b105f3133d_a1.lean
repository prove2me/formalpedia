-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound__p2m_85ec4d12_af4e_4e6b_adb3_c8b105f3133d_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_85ec4d12_af4e_4e6b_adb3_c8b105f3133d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:53:54.433527+00:00
-- url     : https://prove2.me/theorems/d1363084-cb27-469e-84cf-344c4c7f4877
-- title:
--   Drawable supergraph edge lower bound
-- statement:
--   Any drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with at least `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_85ec4d12_af4e_4e6b_adb3_c8b105f3133d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ [DecidableRel K.Adj],
        3 * Fintype.card V - 6 ≤ K.edgeFinset.card) := by sorry
