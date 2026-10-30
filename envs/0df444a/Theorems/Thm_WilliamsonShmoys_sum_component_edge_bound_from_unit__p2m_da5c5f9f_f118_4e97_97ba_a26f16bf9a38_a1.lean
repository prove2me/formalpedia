-- Prove2me | Theorems.Thm_WilliamsonShmoys_sum_component_edge_bound_from_unit__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1
-- name    : WilliamsonShmoys.sum_component_edge_bound_from_unit__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:22:43.170081+00:00
-- url     : https://prove2.me/theorems/4529c8d6-5fd3-4968-a071-d799f95172ad
-- title:
--   Aggregate a unit bound above the total-size threshold
-- statement:
--   If each edge count is at most its corresponding size and the total size is at least three, then the total edge count plus six is at most three times the total size.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.sum_component_edge_bound_from_unit__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1
    {ι : Type} (parts : Finset ι) (c e : ι → Nat)
    (htotal : 3 ≤ ∑ i ∈ parts, c i)
    (hpoint : ∀ i ∈ parts, e i ≤ c i) :
    (∑ i ∈ parts, e i) + 6 ≤ 3 * (∑ i ∈ parts, c i) := by sorry
