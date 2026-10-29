-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count_7369a359__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a2__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a3
-- name    : WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a2__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:21:24.906849+00:00
-- url     : https://prove2.me/theorems/e54967e0-7450-4934-8f48-f373227ab333
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on a finite ordered vertex type of size at least three has exactly three times the number of vertices minus six edges. This isolates the topological edge-count step from the parent’s finite maximization argument. A proof route is to show maximality forces every face to be triangular, then count vertices, edges, and faces using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a2__p2m_57f967cc_933c_4757_9db5_f93a97c57bfc_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hMax : forall N : SimpleGraph V, L <= N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N <= L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
