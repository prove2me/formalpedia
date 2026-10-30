-- Prove2me | Theorems.Thm_WilliamsonShmoys_sum_component_edge_bound_from_witness__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1
-- name    : WilliamsonShmoys.sum_component_edge_bound_from_witness__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:22:41.76542+00:00
-- url     : https://prove2.me/theorems/5042bc88-5ee6-4cf3-a069-61a274dc47d4
-- title:
--   Aggregate a pointwise bound with one six-unit witness
-- statement:
--   If each summand is bounded by three times its corresponding size, and one summand has six units of slack, the finite sums have six units of slack.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.sum_component_edge_bound_from_witness__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1
    {ι : Type} (parts : Finset ι) (c e : ι → Nat)
    (hpoint : ∀ i ∈ parts, e i ≤ 3 * c i)
    (hwitness : ∃ i ∈ parts, e i + 6 ≤ 3 * c i) :
    (∑ i ∈ parts, e i) + 6 ≤ 3 * (∑ i ∈ parts, c i) := by sorry
