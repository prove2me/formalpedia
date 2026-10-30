-- Prove2me | Theorems.Thm_WilliamsonShmoys_unreachable_pair_of_disconnected__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a4
-- name    : WilliamsonShmoys.unreachable_pair_of_disconnected__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:40.82457+00:00
-- url     : https://prove2.me/theorems/ce77cf45-7d4f-4388-9278-a419121a62d9
-- title:
--   Disconnected graphs have an unreachable pair
-- statement:
--   A disconnected finite graph with at least three vertices has two vertices with no path between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.unreachable_pair_of_disconnected__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a4
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hdisc : ¬ H.Connected) :
    ∃ u v : V, ¬ Relation.ReflTransGen H.Adj u v := by sorry
