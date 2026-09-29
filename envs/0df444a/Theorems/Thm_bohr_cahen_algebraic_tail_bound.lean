-- Prove2me | Theorems.Thm_bohr_cahen_algebraic_tail_bound
-- name    : bohr_cahen_algebraic_tail_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T06:27:37.866504+00:00
-- url     : https://prove2.me/theorems/e8443612-43e3-4e3b-bb57-35dedc526b49
-- title:
--   Bohr–Cahen algebraic tail decay via Abel summation
-- statement:
--   If the randomized partial series at $s_0$ is uniformly bounded by $M_P$ over all $N$ and phase paths $\omega$, then Abel summation by parts gives an algebraic tail bound uniform in $\omega$: for $\Re s > \Re s_0$ and $0 < m \le N$, the tail $\sum_{m \le n \le N} \mu(n) X(n,P,\omega) n^{-s}$ is bounded by $M_P (2 + \|s - s_0\| + \|s - s_0\| / (\Re s - \Re s_0))\, m^{\Re s_0 - \Re s}$.

import Mathlib
import Definitions.Def_timepiece_corrector
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

theorem bohr_cahen_algebraic_tail_bound (P : ℕ) (s s₀ : ℂ) (hs : s.re > s₀.re)
    (M_P : ℝ) (hM_nonneg : 0 ≤ M_P) :
    ∀ (ω : Ω_infty), (∀ N, ‖S_recip_random N P s₀ ω‖ ≤ M_P) →
    ∀ m N, 0 < m → m ≤ N →
      ‖∑ n ∈ Icc m N, ((μ n : ℂ) * X_mult n P ω) / (n ^ s)‖ ≤
      (M_P * (2 + ‖s - s₀‖ + ‖s - s₀‖ / (s.re - s₀.re))) *
        (m : ℝ) ^ (s₀.re - s.re) := by sorry
