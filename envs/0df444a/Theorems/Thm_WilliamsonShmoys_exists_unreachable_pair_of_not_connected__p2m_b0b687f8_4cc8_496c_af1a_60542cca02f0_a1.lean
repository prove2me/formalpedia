-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_not_connected__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
-- name    : WilliamsonShmoys.exists_unreachable_pair_of_not_connected__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:24.329519+00:00
-- url     : https://prove2.me/theorems/a3ba6919-e89b-4c92-a770-3dae39df44cc
-- title:
--   Disconnected graph has an unreachable pair
-- statement:
--   If a graph is not connected, there are two vertices that are not joined by a path.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_unreachable_pair_of_not_connected__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (h : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
