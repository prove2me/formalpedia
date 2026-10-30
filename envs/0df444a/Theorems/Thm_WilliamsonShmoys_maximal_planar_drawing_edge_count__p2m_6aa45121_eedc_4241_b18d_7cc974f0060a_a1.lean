-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:35:38.60068+00:00
-- url     : https://prove2.me/theorems/fe266be1-b394-4319-ae10-b52cb17a5e91
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   An inclusion-maximal drawable finite simple graph on at least three vertices has exactly `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
