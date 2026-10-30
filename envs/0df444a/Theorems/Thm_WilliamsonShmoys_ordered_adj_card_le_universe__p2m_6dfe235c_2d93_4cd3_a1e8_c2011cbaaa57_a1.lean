-- Prove2me | Theorems.Thm_WilliamsonShmoys_ordered_adj_card_le_universe__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1
-- name    : WilliamsonShmoys.ordered_adj_card_le_universe__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:17:18.705209+00:00
-- url     : https://prove2.me/theorems/e61b4d3a-4502-453e-8fc3-a98fc3bc4dfd
-- title:
--   Ordered adjacent-pair count is bounded by all ordered pairs
-- statement:
--   The cardinality of the subtype of ordered vertex pairs that are adjacent is at most the cardinality of all ordered vertex pairs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.ordered_adj_card_le_universe__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1 {V : Type} [Fintype V] (G : SimpleGraph V) : Nat.card {p : V × V // G.Adj p.1 p.2} ≤ Nat.card (V × V) := by sorry
