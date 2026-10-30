-- Prove2me | Theorems.Thm_WilliamsonShmoys_sum_component_edge_bounds__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1
-- name    : WilliamsonShmoys.sum_component_edge_bounds__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:56:34.372663+00:00
-- url     : https://prove2.me/theorems/881b0b4b-074b-4163-bcb4-a0dfae9e1f87
-- title:
--   Aggregate component edge bounds
-- statement:
--   For a finite family of nonempty components with total size at least three, if components of size at most two have at most one edge and larger components satisfy the local three-times-size bound with allowance six, then the summed edge count satisfies the same global bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.sum_component_edge_bounds__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1 {ι : Type} [Fintype ι] (n e : ι → Nat) (hpos : ∀ i, 1 ≤ n i) (hN : 3 ≤ ∑ i, n i) (hsmall : ∀ i, n i ≤ 2 → e i ≤ 1) (hlarge : ∀ i, 3 ≤ n i → e i + 6 ≤ 3 * n i) : (∑ i, e i) + 6 ≤ 3 * (∑ i, n i) := by sorry
