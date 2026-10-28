-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_not_reachable_of_not_connected
-- name    : WilliamsonShmoys.exists_not_reachable_of_not_connected
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T10:21:43.694393+00:00
-- url     : https://prove2.me/theorems/c4364f45-8204-43dd-8840-a156d4441cb4
-- title:
--   A disconnected graph has an unreachable pair
-- statement:
--   A graph that is not connected has a pair of vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.exists_not_reachable_of_not_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
