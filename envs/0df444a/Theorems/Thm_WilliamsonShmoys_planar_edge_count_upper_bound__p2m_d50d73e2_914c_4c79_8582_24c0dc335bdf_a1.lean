-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d50d73e2_914c_4c79_8582_24c0dc335bdf_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d50d73e2_914c_4c79_8582_24c0dc335bdf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:15:23.273169+00:00
-- url     : https://prove2.me/theorems/fa13a70a-f07b-4cf3-b92f-4d7140819b58
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every simple graph with a crossing-free drawing on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d50d73e2_914c_4c79_8582_24c0dc335bdf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
