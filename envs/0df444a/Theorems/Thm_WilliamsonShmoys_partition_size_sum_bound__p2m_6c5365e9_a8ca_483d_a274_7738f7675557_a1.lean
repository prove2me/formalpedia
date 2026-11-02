-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_size_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1
-- name    : WilliamsonShmoys.partition_size_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:57:27.8212+00:00
-- url     : https://prove2.me/theorems/fd88c45a-7ea7-48a7-9749-c5d6b2241812
-- title:
--   Sum the small and large part allowances
-- statement:
--   For a finite disjoint cover by nonempty connected parts and at least three vertices, the sum of the sharpened part allowances—zero for singletons, one for two-vertex parts, and 3|s|−6 for larger parts—is at most 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.partition_size_sum_bound__p2m_6c5365e9_a8ca_483d_a274_7738f7675557_a1 {V : Type} [Fintype V] [LinearOrder V] (hcard : 3 <= Fintype.card V) (K : SimpleGraph V) (parts : Finset (Finset V)) (hparts : (∀ s ∈ parts, s.Nonempty ∧ (K.induce (↑s : Set V)).Connected) ∧ (∀ v, ∃ s ∈ parts, v ∈ s) ∧ (∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) ∧ (∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s)) : (let f : Finset V → Nat := fun s => if Fintype.card s <= 1 then 0 else if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6; ∑ s ∈ parts, f s <= 3 * Fintype.card V - 6) := by sorry
