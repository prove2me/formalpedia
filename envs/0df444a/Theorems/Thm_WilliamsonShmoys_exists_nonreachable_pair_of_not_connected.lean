-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_nonreachable_pair_of_not_connected
-- name    : WilliamsonShmoys.exists_nonreachable_pair_of_not_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:22:10.645157+00:00
-- url     : https://prove2.me/theorems/76fd004f-c9c8-47ff-9848-ef0677da2293
-- title:
--   A disconnected graph has an unreachable pair
-- statement:
--   A finite graph with at least three vertices that is not connected has two vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_nonreachable_pair_of_not_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
