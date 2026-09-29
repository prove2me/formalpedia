-- Prove2me | Theorems.Thm_BanditAlgorithm_asymptotic_ucb_finite_bound_limsup
-- name    : BanditAlgorithm.asymptotic_ucb_finite_bound_limsup
-- status  : Proved
-- author  : @ann
-- created : 2026-07-19T05:15:05.972306+00:00
-- url     : https://prove2.me/theorems/0e888bfd-e64f-4800-ac1b-26618bd9c62b
-- title:
--   Finite UCB bound implies the asymptotic limsup constant
-- statement:
--   Let $R_n$ be any real sequence and let $\Delta_i$ be finitely many gaps. Assume that for every horizon and every armwise choice $0<\varepsilon_i<\Delta_i$, $R_n$ obeys the finite-time bound in Eq. (8.1) with $f(n)=1+n\log^2 n$. Then
--
--   $$\limsup_{n\to\infty} \operatorname{ofReal}\!\left(\frac{R_n}{\log n}\right) \le \sum_{i:\Delta_i>0} \operatorname{ofReal}\!\left(\frac{2}{\Delta_i}\right).$$
--
--   This isolates the purely analytic final step of Theorem 8.1: choose $\varepsilon_i=\log(n)^{-1/4}$ once it is smaller than every positive gap, divide by $\log n$, and let $n$ tend to infinity. Zero or nonpositive gaps are excluded by the same finite filter as in the source, including the empty-filter boundary case.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 8.1, final sentence on printed p. 120 / PDF p. 129, following Eqs. (8.1)-(8.4): choose epsilon = log(n)^(-1/4) and take the limit.

import Definitions.Def_asymptoticUcbPolicy

open Filter

theorem BanditAlgorithm.asymptotic_ucb_finite_bound_limsup {k : ℕ}
    (R : ℕ → ℝ) (Δ : Fin k → ℝ)
    (hR : ∀ (n : ℕ) (ε : Fin k → ℝ),
      (∀ i, 0 < Δ i → 0 < ε i ∧ ε i < Δ i) →
      R n ≤
        ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i),
          Δ i *
            (1 + 5 / (ε i) ^ 2 +
              2 / (Δ i - ε i) ^ 2 *
                (Real.log (asymptoticUcbSchedule n) +
                  Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) + 1))) :
    atTop.limsup (fun n : ℕ ↦ ENNReal.ofReal (R n / Real.log n)) ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i),
        ENNReal.ofReal (2 / Δ i) := by
  sorry
