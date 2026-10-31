-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_triangle_count__p2m_2a0eb6c3_e8b8_46c5_bb28_c648f00dcb7f_a1
-- name    : WilliamsonShmoys.maximal_planar_euler_triangle_count__p2m_2a0eb6c3_e8b8_46c5_bb28_c648f00dcb7f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:46:59.231501+00:00
-- url     : https://prove2.me/theorems/17eb0fc8-3683-4688-9bd5-07f26a4d1b81
-- title:
--   Euler and triangular-face counts for a maximal planar drawing
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type, there is a natural number of faces satisfying Euler’s vertex-edge-face equation and the triangular-face edge-incidence equation. The first equation records Euler’s formula for a connected plane embedding; the second records that every face boundary has length three and every edge is counted twice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_euler_triangle_count__p2m_2a0eb6c3_e8b8_46c5_bb28_c648f00dcb7f_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
