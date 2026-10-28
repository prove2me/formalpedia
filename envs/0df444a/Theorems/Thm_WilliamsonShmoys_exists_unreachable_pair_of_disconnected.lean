-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_disconnected
-- name    : WilliamsonShmoys.exists_unreachable_pair_of_disconnected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:05:15.363886+00:00
-- url     : https://prove2.me/theorems/4d06dfc0-c97f-43c6-9587-fc25491aa9ec
-- title:
--   A nonempty disconnected graph has an unreachable pair
-- statement:
--   For a finite nonempty graph that is not connected, some pair of vertices is not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_unreachable_pair_of_disconnected
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hNonempty : 0 < Fintype.card V)
    (hNotConnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
