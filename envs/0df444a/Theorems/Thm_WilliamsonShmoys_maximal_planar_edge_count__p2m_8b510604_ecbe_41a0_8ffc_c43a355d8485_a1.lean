-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:07.936507+00:00
-- url     : https://prove2.me/theorems/dafc8434-c658-484f-b8e8-b76293ec5b82
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A connected planar graph on at least three vertices that is maximal among planar supergraphs on the same vertex set has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel _
    (∀ K : SimpleGraph V,
      (letI : DecidableRel K.Adj := Classical.decRel _;
       H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)) →
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
