-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:12:24.325878+00:00
-- url     : https://prove2.me/theorems/87c340c3-322c-4d0b-a13d-05f0d4bff66a
-- title:
--   Maximal planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices that has no drawable supergraph with additional edges has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
