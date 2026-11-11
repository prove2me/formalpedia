-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_allowance_sum_large_family__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a1
-- name    : WilliamsonShmoys.partition_allowance_sum_large_family__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:16.668913+00:00
-- url     : https://prove2.me/theorems/0659cd6c-187b-4fc2-a352-b53a05d4e1ab
-- title:
--   Allowance bound for multiple nonempty parts
-- statement:
--   If at least two nonempty finite parts have total size |V|, with |V| at least three, then the sum of the specified small-part and large-part allowances is at most 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.partition_allowance_sum_large_family__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a1 {V : Type} [Fintype V] (parts : Finset (Finset V)) (hnonempty : ∀ s ∈ parts, s.Nonempty) (hparts : 2 ≤ parts.card) (hsum : (∑ s ∈ parts, s.card) = Fintype.card V) (hcard : 3 ≤ Fintype.card V) : (let f : Finset V → Nat := fun s => if Fintype.card s ≤ 1 then 0 else if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6; ∑ s ∈ parts, f s ≤ 3 * Fintype.card V - 6) := by sorry
