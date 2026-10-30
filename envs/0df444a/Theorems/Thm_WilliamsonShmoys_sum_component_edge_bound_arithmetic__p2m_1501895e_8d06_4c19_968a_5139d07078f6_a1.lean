-- Prove2me | Theorems.Thm_WilliamsonShmoys_sum_component_edge_bound_arithmetic__p2m_1501895e_8d06_4c19_968a_5139d07078f6_a1
-- name    : WilliamsonShmoys.sum_component_edge_bound_arithmetic__p2m_1501895e_8d06_4c19_968a_5139d07078f6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:41.121811+00:00
-- url     : https://prove2.me/theorems/da5c5f9f-f118-4e97-97ba-a26f16bf9a38
-- title:
--   Finite-sum component edge bound
-- statement:
--   For a finite family with total size at least three, suppose each large member's edge count has six units of slack against three times its size, and each member of size below three has at most its size minus one edges. Then the total edge count plus six is at most three times the total size. The lemma also covers zero-size members under truncated natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.sum_component_edge_bound_arithmetic__p2m_1501895e_8d06_4c19_968a_5139d07078f6_a1
    {ι : Type} (parts : Finset ι) (c e : ι → Nat)
    (htotal : 3 ≤ ∑ i ∈ parts, c i)
    (hlarge : ∀ i ∈ parts, 3 ≤ c i → e i + 6 ≤ 3 * c i)
    (hsmall : ∀ i ∈ parts, c i < 3 → e i ≤ c i - 1) :
    (∑ i ∈ parts, e i) + 6 ≤ 3 * (∑ i ∈ parts, c i) := by sorry
