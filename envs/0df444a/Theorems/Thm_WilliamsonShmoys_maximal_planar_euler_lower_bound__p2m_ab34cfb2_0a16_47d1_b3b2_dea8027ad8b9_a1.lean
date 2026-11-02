-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_lower_bound__p2m_ab34cfb2_0a16_47d1_b3b2_dea8027ad8b9_a1
-- name    : WilliamsonShmoys_maximal_planar_euler_lower_bound__p2m_ab34cfb2_0a16_47d1_b3b2_dea8027ad8b9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:58:54.093493+00:00
-- url     : https://prove2.me/theorems/2d07592e-de05-4bbe-bc2f-be57428238dd
-- title:
--   Maximality forces the planar edge lower bound
-- statement:
--   A connected graph that is inclusion-maximal among graphs on the same finite vertex type admitting a crossing-free drawing, with at least three vertices, has at least three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_maximal_planar_euler_lower_bound__p2m_ab34cfb2_0a16_47d1_b3b2_dea8027ad8b9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V ≤ K.edgeFinset.card + 6 := by sorry
