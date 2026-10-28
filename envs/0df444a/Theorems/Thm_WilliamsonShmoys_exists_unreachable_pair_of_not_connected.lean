-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_not_connected
-- name    : WilliamsonShmoys.exists_unreachable_pair_of_not_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:27:24.71466+00:00
-- url     : https://prove2.me/theorems/ec75aea8-fa5f-4321-9232-608919d93c16
-- title:
--   A disconnected finite graph has an unreachable pair
-- statement:
--   A finite graph on at least three vertices that is not connected has a pair of vertices with no path between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_unreachable_pair_of_not_connected
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hdis : Not G.Connected) :
    Exists fun u : V => Exists fun v : V => Not (G.Reachable u v) := by
  sorry
