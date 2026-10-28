-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_partition_edge_slack
-- name    : WilliamsonShmoys.finite_partition_edge_slack
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:48:07.771507+00:00
-- url     : https://prove2.me/theorems/2276a8a6-88fb-4c30-a65f-2ca01bcf7b41
-- title:
--   Aggregate slack over finite component indices
-- statement:
--   For a finite family of component sizes and edge counts, the small-part and large-part bounds imply six units of total slack when the total size is at least three. If every part is small, sum e ≤ v and use 6 ≤ 2 times the total size. If some part i is large, add six only to e i: its pointwise bound follows from hlarge, and every other part has e j ≤ 3v j by hsmall or hlarge. Summing gives the result. This handles the arithmetic split needed by the parent without assuming a large component exists.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_partition_edge_slack
    {ι : Type} [Fintype ι]
    (v e : ι → Nat)
    (hv : 3 ≤ ∑ i, v i)
    (hsmall : ∀ i, v i < 3 → e i ≤ v i)
    (hlarge : ∀ i, 3 ≤ v i → e i + 6 ≤ 3 * v i) :
    (∑ i, e i) + 6 ≤ 3 * (∑ i, v i) := by sorry
