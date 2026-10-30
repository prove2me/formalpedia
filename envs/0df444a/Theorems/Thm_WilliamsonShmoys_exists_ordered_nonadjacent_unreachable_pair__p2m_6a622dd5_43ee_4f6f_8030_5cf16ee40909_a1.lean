-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_ordered_nonadjacent_unreachable_pair__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1
-- name    : WilliamsonShmoys.exists_ordered_nonadjacent_unreachable_pair__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:51.412829+00:00
-- url     : https://prove2.me/theorems/e537c147-772d-43a5-b4b3-bf0f040dc6a0
-- title:
--   Disconnectedness supplies an ordered nonadjacent pair in distinct reachability classes
-- statement:
--   A nonempty finite disconnected graph has an ordered pair of vertices that are nonadjacent and not reachable from one another. This removes the graph-theoretic choice of endpoints from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_ordered_nonadjacent_unreachable_pair__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 0 < Fintype.card V) (hDisconnected : ¬ H.Connected) : ∃ u v : V, u < v ∧ ¬ H.Adj u v ∧ ¬ H.Reachable u v := by sorry
