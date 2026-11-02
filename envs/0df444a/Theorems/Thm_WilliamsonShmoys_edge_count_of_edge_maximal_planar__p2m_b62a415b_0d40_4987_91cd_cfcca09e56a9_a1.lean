-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1
-- name    : WilliamsonShmoys.edge_count_of_edge_maximal_planar__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:49:49.713384+00:00
-- url     : https://prove2.me/theorems/40182049-fc6a-4cfb-9899-f86d953b2959
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_edge_maximal_planar__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
