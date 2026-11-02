-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_block_edge_bound_aggregation__p2m_a70877ba_ee67_4eb5_a950_6d5f423393ca_a2
-- name    : WilliamsonShmoys.finite_block_edge_bound_aggregation__p2m_a70877ba_ee67_4eb5_a950_6d5f423393ca_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:47:03.912061+00:00
-- url     : https://prove2.me/theorems/731c12b2-a7c8-4762-9428-5f2daf164604
-- title:
--   Aggregate local edge bounds over finite blocks
-- statement:
--   If all blocks are nonempty, singleton and pair blocks satisfy their direct edge bounds, and every block of size at least three has six units of local slack, then the total edge sum plus six is bounded by three times the total size. A large block supplies the global slack; if there is none, the total edge sum is at most the total size and the total-size lower bound supplies the inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_block_edge_bound_aggregation__p2m_a70877ba_ee67_4eb5_a950_6d5f423393ca_a2
    {α : Type} (C : Finset α) (n e : α → Nat)
    (hn : ∀ a ∈ C, 0 < n a)
    (he1 : ∀ a ∈ C, n a = 1 → e a = 0)
    (he2 : ∀ a ∈ C, n a = 2 → e a ≤ 1)
    (hebig : ∀ a ∈ C, 3 ≤ n a → e a + 6 ≤ 3 * n a)
    (htotal : 3 ≤ ∑ a ∈ C, n a) :
    (∑ a ∈ C, e a) + 6 ≤ 3 * (∑ a ∈ C, n a) := by sorry
