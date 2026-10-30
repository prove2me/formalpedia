-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_ncard__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_ncard__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:55:54.843373+00:00
-- url     : https://prove2.me/theorems/81f5bc0c-f9d2-498a-8992-3186a8a606eb
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite ordered vertices that has no drawable proper supergraph has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_ncard__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
