-- Prove2me | Theorems.Thm_gpy_mertensMuSqSum_bound_of_S0
-- name    : gpy_mertensMuSqSum_bound_of_S0
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T08:00:24.528628+00:00
-- url     : https://prove2.me/theorems/8be5d55c-0a33-49a1-9f6f-9666cb41f587
-- title:
--   Conditional Mertens bound: an S0 bound implies the general S_m bound
-- statement:
--   CONDITIONAL statement. Assume a constant \(C_0 \ge 0\) such that for every i, the partial sum \(\sum_{D \le i} \mu(D)^2/\varphi(D)\) differs from \(\log i\) by at most \(C_0\). Then for every m and T, the log-power sum \(\sum_{D \le T} \mu(D)^2/\varphi(D) \cdot (\log D)^m\) differs from \((\log T)^{m+1}/(m+1)\) by at most \((6 + 2 C_0) (\log T)^m\). The constant \(1/(m+1)\) is exact. The S0 bound itself is a hypothesis of this theorem and is NOT proved by it; nothing here asserts that any such \(C_0\) exists. Formalization Note: the weight \(\mu(D)^2/\varphi(D)\) on squarefree D (0 otherwise) and both sums are written out in Mathlib terms, with no local definitions.
-- source:
--   GPY Mertens partial: harmonic log-power bound and the conditional bridge from an S0 bound to the general S_m bound

import Mathlib
open Classical

theorem gpy_mertensMuSqSum_bound_of_S0 (m : ℕ) (T : ℕ) (C₀ : ℝ)
    (hC₀ : 0 ≤ C₀)
    (hS0 : ∀ i : ℕ,
      abs ((∑ D ∈ Finset.range (i + 1), (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
        / ((Nat.totient D : ℕ) : ℝ) else 0)) - Real.log (i : ℝ)) ≤ C₀) :
    abs ((∑ D ∈ Finset.range (T + 1),
      (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
        / ((Nat.totient D : ℕ) : ℝ) else 0) * (Real.log (D : ℝ)) ^ m)
      - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ (6 + 2 * C₀) * (Real.log (T : ℝ)) ^ m := by sorry
