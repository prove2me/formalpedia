-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_piecewise_sum_bound_large_aggregate
-- name    : WilliamsonShmoys.finite_piecewise_sum_bound_large_aggregate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:43:52.429118+00:00
-- url     : https://prove2.me/theorems/e57c6352-f641-4017-aa4b-6865d727e199
-- title:
--   Finite sum bound with one six-unit margin
-- statement:
--   For a finite family, if every value is at most three times its size and one included element has an additional margin of 6, then the aggregate has that same margin. In the target’s large-size branch, the witness with size at least 3 supplies this margin; sizes below 3 still satisfy the general bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_piecewise_sum_bound_large_aggregate {α : Type} [Fintype α] (s : Finset α) (a b : α → Nat) (x : α) (hx : x ∈ s) (hAll : ∀ y ∈ s, b y ≤ 3 * a y) (hMargin : b x + 6 ≤ 3 * a x) : s.sum b + 6 ≤ 3 * (s.sum a) := by sorry
