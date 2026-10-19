-- Prove2me | Theorems.Thm_dusart_theta_mesh_analytic_completion
-- name    : dusart_theta_mesh_analytic_completion
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T05:00:36.222732+00:00
-- url     : https://prove2.me/theorems/c2a43e00-f8a1-454a-a0fe-266d6a503ee2
-- title:
--   Analytic completion of the finite theta mesh certificate
-- statement:
--   Let $\theta$ denote the Chebyshev theta function. Suppose a bound $10^6\theta(10^8)\le99989691935170$ implies both the terminal carry $10^6\theta(10000064768)\le10000013784295984$ and $\theta(x)\le x+100000+x/10000$ for every $10^8\le x<10000064768$. For every integer $32\le n\le\lceil16e^{23}\rceil$, set $a=n/16$ and $b=(n+1)/16$. Then
--
--   $$|\theta(a)-a|\le\frac{1513a}{10\log^4 b},\qquad |\theta(a)-b|\le\frac{1513a}{10\log^4 b}.$$
--
--   This is the analytic implication that completes the finite mesh certificate from the specified large-interval upper bound.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite-certificate formalization.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Exp

theorem dusart_theta_mesh_analytic_completion (hc : (1000000 : ℝ) * Chebyshev.theta 100000000 ≤ 99989691935170 →
    (1000000 : ℝ) * Chebyshev.theta 10000064768 ≤ 10000013784295984 ∧
    ∀ x : ℝ, 100000000 ≤ x → x < 10000064768 →
      Chebyshev.theta x ≤ x + 100000 + x / 10000)
    (n : ℕ) (hn : 32 ≤ n) (hcap : n ≤ Nat.ceil (16 * Real.exp 23)) :
    let a : ℝ := (n : ℝ) / 16
    let b : ℝ := ((n : ℝ) + 1) / 16
    |Chebyshev.theta a - a| ≤ (1513 / 10 : ℝ) * a / (Real.log b)^4 ∧
      |Chebyshev.theta a - b| ≤ (1513 / 10 : ℝ) * a / (Real.log b)^4 := by sorry
