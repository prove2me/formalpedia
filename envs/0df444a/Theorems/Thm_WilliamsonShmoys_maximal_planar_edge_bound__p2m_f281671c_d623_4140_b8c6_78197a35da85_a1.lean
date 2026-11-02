-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:56:11.807048+00:00
-- url     : https://prove2.me/theorems/85779ab4-eea1-45b5-a2d8-374ad848250a
-- title:
--   Edge bound for maximal drawable graphs
-- statement:
--   An inclusion-maximal simple graph with the stated finite crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := dH; H.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by sorry
