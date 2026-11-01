-- Prove2me | Theorems.Thm_gpy_mertensS0_bound_aux
-- name    : gpy_mertensS0_bound_aux
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T18:36:10.096655+00:00
-- url     : https://prove2.me/theorems/cd199787-5ba6-464b-a2ed-db5b8d69e2b2
-- title:
--   The S0 bound in sharp form, 51 * exp 2
-- statement:
--   For every natural number \(T \geq 2\), the partial sum \(S_0(T) = \sum_{D \leq T} \mu^2(D)/\varphi(D)\) differs from \(\log T\) by at most \(51e^2\). The proof is elementary: writing \(b(n) = \mu^2(n)n/\varphi(n)\) as the Dirichlet convolution of \(1\) with a factor \(c\) supported on prime powers \(p\) and \(p^2\), the sum becomes a harmonic sum weighted by \(c(d)/d\), and truncated Euler products bound both the absolute and log-weighted \(c\)-sums. No prime number theorem or Chebyshev estimate is used; only convergent prime sums and the harmonic bound. Formalization Note: the sum is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY S0 bound: sharp form of the explicit Mertens input for hMono

import Mathlib
open Classical

theorem gpy_mertensS0_bound_aux {T : ℕ} (hT : 2 ≤ T) :
    abs ((∑ D ∈ Finset.range (T + 1), (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
      / ((Nat.totient D : ℕ) : ℝ) else 0)) - Real.log (T : ℝ))
      ≤ 51 * Real.exp 2 := by sorry
