-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_not_connected__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2
-- name    : WilliamsonShmoys.exists_unreachable_pair_of_not_connected__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T12:53:03.619002+00:00
-- url     : https://prove2.me/theorems/5f6c1505-f53f-432c-8004-e1bd4bff5999
-- title:
--   A disconnected finite graph has an unreachable pair
-- statement:
--   A finite graph that is not connected has a pair of vertices that are not reachable from each other.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.exists_unreachable_pair_of_not_connected__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
