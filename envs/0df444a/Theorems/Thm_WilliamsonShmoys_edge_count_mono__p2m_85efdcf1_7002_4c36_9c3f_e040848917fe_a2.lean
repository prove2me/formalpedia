-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_mono__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
-- name    : WilliamsonShmoys_edge_count_mono__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:48:33.66051+00:00
-- url     : https://prove2.me/theorems/97515466-b516-4d99-96b6-928afdd87a93
-- title:
--   Monotonicity of edge count under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, graph inclusion implies inclusion of edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_edge_count_mono__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
