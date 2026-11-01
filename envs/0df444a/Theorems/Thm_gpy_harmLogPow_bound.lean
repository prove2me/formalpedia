-- Prove2me | Theorems.Thm_gpy_harmLogPow_bound
-- name    : gpy_harmLogPow_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T07:57:19.792129+00:00
-- url     : https://prove2.me/theorems/879c6b51-c617-421e-9741-c1f7a79b032d
-- title:
--   Harmonic log-power bound with exact constant 2
-- statement:
--   For every m and T, the harmonic log-power sum \(\sum_{1 \le e \le T} (\log e)^m / e\) differs from the main term \((\log T)^{m+1}/(m+1)\) by at most \(2 (\log T)^m\). The proof is elementary telescoping, using the power-difference sandwich and \(1/(k+1) \le \log(1+1/k) \le 1/k\); no prime-number input, Chebyshev bound, or Mertens input is used. Formalization Note: the sum is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY Mertens partial: harmonic log-power bound and the conditional bridge from an S0 bound to the general S_m bound

import Mathlib
open Classical

theorem gpy_harmLogPow_bound (m : ℕ) (T : ℕ) :
    abs ((∑ e ∈ Finset.Icc 1 T, (Real.log (e : ℝ)) ^ m / (e : ℝ))
      - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ 2 * (Real.log (T : ℝ)) ^ m := by sorry
