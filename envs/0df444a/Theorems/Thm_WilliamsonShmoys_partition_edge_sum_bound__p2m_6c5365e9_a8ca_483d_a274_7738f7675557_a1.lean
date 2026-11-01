-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_edge_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1
-- name    : WilliamsonShmoys.partition_edge_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:54:42.762389+00:00
-- url     : https://prove2.me/theorems/dcaefdba-b10e-4220-bda1-55f53e9c0d30
-- title:
--   Bound graph edges by the sum of connected part bounds
-- statement:
--   Under the partition conditions and local induced-subgraph bounds, the total edge count is at most the sum of the sharper per-part contributions: zero for parts of size at most one, one for size two, and the local bound for larger parts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.partition_edge_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hlocal : ∀ (s : Finset V), (K.induce (↑s : Set V)).Connected → (letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _; (K.induce (↑s : Set V)).edgeFinset.card ≤ max 1 (3 * Fintype.card s - 6))) (parts : Finset (Finset V)) (hparts : (∀ s ∈ parts, s.Nonempty ∧ (K.induce (↑s : Set V)).Connected) ∧ (∀ v, ∃ s ∈ parts, v ∈ s) ∧ (∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) ∧ (∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s)) : (letI : DecidableRel K.Adj := Classical.decRel K.Adj; let f : Finset V → Nat := fun s => if Fintype.card s ≤ 1 then 0 else if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6; K.edgeFinset.card ≤ ∑ s ∈ parts, f s) := by sorry
