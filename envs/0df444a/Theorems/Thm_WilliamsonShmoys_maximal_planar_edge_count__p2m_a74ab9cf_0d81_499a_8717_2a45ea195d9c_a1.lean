-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
-- name    : WilliamsonShmoys_maximal_planar_edge_count__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:25.523065+00:00
-- url     : https://prove2.me/theorems/ab34cfb2-0a16-47d1-b3b2-dea8027ad8b9
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A maximal planar graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys_maximal_planar_edge_count__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hconn : K.Connected)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V = K.edgeFinset.card + 6 := by sorry
