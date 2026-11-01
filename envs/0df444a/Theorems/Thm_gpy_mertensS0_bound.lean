-- Prove2me | Theorems.Thm_gpy_mertensS0_bound
-- name    : gpy_mertensS0_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T18:38:56.064429+00:00
-- url     : https://prove2.me/theorems/c9507ae9-e92c-4265-afc3-5d6c63bab766
-- title:
--   The S0 bound with explicit constant 500
-- statement:
--   For every natural number \(i\), the partial sum \(S_0(i) = \sum_{D \leq i} \mu^2(D)/\varphi(D)\) differs from \(\log i\) by at most \(500\). The constant \(500\) is fully explicit: it comes from the sharper bound \(51e^2\) together with \(e < 3\). The proof is elementary, via the Dirichlet convolution \(b = 1 * c\) with \(c(p) = 1/(p-1)\), \(c(p^2) = -p/(p-1)\), and \(c(p^k) = 0\) for \(k \geq 3\), plus truncated Euler product bounds; no prime number theorem or Chebyshev estimate is used. This discharges the \(S_0\) hypothesis of the conditional bridge to the general one-variable Mertens bound, making the GPY monomial input unconditional. Formalization Note: the sum is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY S0 bound: explicit unconditional Mertens input for hMono

import Mathlib
open Classical

theorem gpy_mertensS0_bound : ∀ i : ℕ,
    abs ((∑ D ∈ Finset.range (i + 1), (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
      / ((Nat.totient D : ℕ) : ℝ) else 0)) - Real.log (i : ℝ)) ≤ 500 := by sorry
