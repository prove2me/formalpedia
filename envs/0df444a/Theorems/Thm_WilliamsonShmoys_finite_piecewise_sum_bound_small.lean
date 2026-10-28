-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_piecewise_sum_bound_small
-- name    : WilliamsonShmoys.finite_piecewise_sum_bound_small
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:43:20.51711+00:00
-- url     : https://prove2.me/theorems/63640e98-e17d-4481-8129-6f047f92565c
-- title:
--   Finite sum bound when all sizes are small
-- statement:
--   If each value is at most its size and the total size is at least 3, then the sum of the values is at most three times the total size minus 6. In the target’s all-small branch, the piecewise hypothesis yields the required pointwise bound, including sizes 0, 1, and 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_piecewise_sum_bound_small {α : Type} [Fintype α] (s : Finset α) (size : α → Nat) (f : α → Nat) (n : Nat) (hPointwise : ∀ x ∈ s, f x ≤ size x) (hSum : s.sum size = n) (hn : 3 ≤ n) : s.sum f ≤ 3 * n - 6 := by sorry
