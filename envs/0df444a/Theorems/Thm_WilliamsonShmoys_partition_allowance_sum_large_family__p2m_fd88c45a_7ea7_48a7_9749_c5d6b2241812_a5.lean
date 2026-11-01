-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_allowance_sum_large_family__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a5
-- name    : WilliamsonShmoys_partition_allowance_sum_large_family__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:23:29.950546+00:00
-- url     : https://prove2.me/theorems/e1cfc50e-addd-48da-a23d-cafc2ece696d
-- title:
--   Allowance sum for multiple nonempty parts
-- statement:
--   For at least two nonempty parts whose cardinalities sum to |V|, with |V| at least three, the sum of the specified singleton, pair, and larger-part allowances is at most 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_partition_allowance_sum_large_family__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a5 {V : Type} [Fintype V] (parts : Finset (Finset V)) (hnonempty : ∀ s ∈ parts, s.Nonempty) (hparts : 2 ≤ parts.card) (hsum : ∑ s ∈ parts, s.card = Fintype.card V) (hcard : 3 ≤ Fintype.card V) : (let f : Finset V → Nat := fun s => if Fintype.card s ≤ 1 then 0 else if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6; ∑ s ∈ parts, f s ≤ 3 * Fintype.card V - 6) := by sorry
