-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_not_connected_of_card_ge_three__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a2
-- name    : WilliamsonShmoys.exists_unreachable_pair_of_not_connected_of_card_ge_three__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:17:24.645274+00:00
-- url     : https://prove2.me/theorems/1cb8985e-ffa6-4201-85bd-669152347d1f
-- title:
--   Disconnected nonempty graph has an unreachable pair
-- statement:
--   For a finite graph with at least three vertices, failure of connectedness yields a pair of vertices with no path between them. The cardinality hypothesis rules out the empty-vertex counterexample to the earlier version of this claim.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_unreachable_pair_of_not_connected_of_card_ge_three__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (h : ¬ G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
