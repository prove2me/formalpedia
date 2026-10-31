-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
-- name    : WilliamsonShmoys_maximal_planar_edge_count__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:48:38.395135+00:00
-- url     : https://prove2.me/theorems/a5abbcfc-8844-40a4-806c-eef213b4f62c
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A connected planar graph that is maximal among planar supergraphs on the same vertex type, with at least three vertices, has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_edge_count__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
