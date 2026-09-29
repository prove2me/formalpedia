-- Prove2me | Theorems.Thm_SmaleNinth_abs_det_le_factorial_mul_pow
-- name    : SmaleNinth.abs_det_le_factorial_mul_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-06T17:54:05.146646+00:00
-- url     : https://prove2.me/theorems/3e3b0bd4-26f0-4182-ae0c-52de2b1bcf99
-- title:
--   Permutation-expansion determinant bound $|\\det M| \\le r!\\,U^r$
-- statement:
--   Let $M \in \mathbb{Z}^{r \times r}$ be a square integer matrix all of whose entries satisfy $|M_{ij}| \le U$. Then
--   $$|\det M| \;\le\; r!\,U^{\,r} .$$
--
--   This is the crude size estimate that accompanies Cramer's rule in the analysis of the bit complexity of linear programming. It follows directly from the Leibniz expansion
--   $$\det M = \sum_{\sigma \in S_r} \operatorname{sgn}(\sigma) \prod_{i} M_{\sigma(i), i} :$$
--   each of the $r!$ summands is a product of $r$ entries and hence bounded by $U^{\,r}$ in absolute value, and the sign contributes a factor of modulus one.
--
--   The bound is far from sharp -- Hadamard's inequality gives the better estimate $r^{r/2} U^{\,r}$ -- but only its polynomial *bit size*, $O(r \log r + r \log U)$, matters in the intended application: together with the fact that a nonsingular integer determinant has absolute value at least $1$, it bounds every coordinate of the Cramer solution of an $r \times r$ integer system by $r!\,U^{\,r}$.
-- source:
--   B. Korte, J. Vygen, Combinatorial Optimization: Theory and Algorithms, 6th ed., Springer 2018, Section 4.1 (Size of Vertices and Faces), proof of Theorem 4.4; A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 3.2 (sizes and good characterizations).

import Mathlib

open Matrix Finset

theorem SmaleNinth.abs_det_le_factorial_mul_pow {r : ℕ} (U : ℕ)
    (M : Matrix (Fin r) (Fin r) ℤ) (hM : ∀ i j, |M i j| ≤ (U : ℤ)) :
    |M.det| ≤ (r.factorial : ℤ) * (U : ℤ) ^ r := by sorry
