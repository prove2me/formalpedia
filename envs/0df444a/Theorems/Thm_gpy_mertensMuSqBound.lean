-- Prove2me | Theorems.Thm_gpy_mertensMuSqBound
-- name    : gpy_mertensMuSqBound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T18:42:09.749989+00:00
-- url     : https://prove2.me/theorems/1658d367-e9df-46d5-a561-336b150b0a62
-- title:
--   Unconditional Mertens bound for mu^2/phi-weighted log-power sums
-- statement:
--   For every \(m\) and \(T\), the one-variable sum \(\sum_{D \leq T} \frac{\mu^2(D)}{\varphi(D)} (\log D)^m\) differs from \(\frac{(\log T)^{m+1}}{m+1}\) by at most \(1006 (\log T)^m\). The constant \(1/(m+1)\) is exact, and the factor \(1006 = 6 + 2 \cdot 500\) comes from the explicit \(S_0\) bound with constant \(500\). The argument is Abel summation against the \(S_0\) bound plus the elementary harmonic bound; no prime number theorem or Chebyshev estimate is used. This is the unconditional one-variable Mertens input for the GPY monomial evaluation (hypothesis hMono). Formalization Note: the sum is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY S0 bound: unconditional one-variable Mertens bound for hMono

import Mathlib
open Classical

theorem gpy_mertensMuSqBound (m T : ℕ) :
    abs ((∑ D ∈ Finset.range (T + 1), (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
      / ((Nat.totient D : ℕ) : ℝ) else 0) * (Real.log (D : ℝ)) ^ m)
      - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ (6 + 2 * 500) * (Real.log (T : ℝ)) ^ m := by sorry
