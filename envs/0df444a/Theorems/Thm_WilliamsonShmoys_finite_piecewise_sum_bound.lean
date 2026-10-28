-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_piecewise_sum_bound
-- name    : WilliamsonShmoys.finite_piecewise_sum_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:38:14.940996+00:00
-- url     : https://prove2.me/theorems/047c3853-1b16-4f0d-87eb-db155dd6c316
-- title:
--   Finite piecewise sum bound
-- statement:
--   For any finite family of natural-number sizes and values whose sizes sum to n, if each value satisfies the given size-dependent allowance and n is at least 3, then the values sum to at most 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_piecewise_sum_bound {α : Type} [Fintype α] (s : Finset α) (size : α → Nat) (f : α → Nat) (n : Nat) (hSum : s.sum size = n) (hPiece : ∀ x ∈ s, f x ≤ (if size x < 3 then size x / 2 else 3 * size x - 6)) (hn : 3 ≤ n) : s.sum f ≤ 3 * n - 6 := by sorry
