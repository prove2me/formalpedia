-- Prove2me | Theorems.Thm_bernoulli_expectation_sqrt_le_sqrt_expectation
-- name    : bernoulli_expectation_sqrt_le_sqrt_expectation
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T14:28:37.694057+00:00
-- url     : https://prove2.me/theorems/8bff3da6-c8fc-4c3d-b5cb-e48836b7d1ca
-- statement:
--   **Square-root Jensen (Cauchy–Schwarz) for the Bernoulli expectation.**
--
--   Fix dimensions $n_1,n_2$ and an inclusion probability $p\in[0,1]$. Let $\mathbb E_p[\cdot]=\sum_\Omega w_p(\Omega)(\cdot)$ denote the Bernoulli expectation, where $w_p(\Omega)=p^{|\Omega|}(1-p)^{N-|\Omega|}$ and $N=n_1n_2$. For every pointwise-nonnegative statistic $F\ge 0$,
--   $$\mathbb E_p\big[\sqrt{F}\big]\ \le\ \sqrt{\mathbb E_p[F]}.$$
--
--   This is the concavity of $\sqrt{\cdot}$ against a probability measure, equivalently the Cauchy–Schwarz inequality
--   $$\Big(\sum_\Omega w_p(\Omega)\sqrt{F(\Omega)}\Big)^2\le\Big(\sum_\Omega w_p(\Omega)\Big)\Big(\sum_\Omega w_p(\Omega)F(\Omega)\Big)=\mathbb E_p[F],$$
--   using that the weights are nonnegative (because $0\le p\le 1$) and sum to $1$ (binomial theorem, $\sum_\Omega w_p(\Omega)=(p+(1-p))^N=1$).
--
--   It is the $q/2$-versus-$q$ power-mean bridge in the conditional-Khintchine matrix-moment estimates: it converts an $\mathbb E_p[Z^q]$ bound into the $\mathbb E_p[Z^{q/2}]$ bound needed for the Rademacher symmetrization scale.
-- source:
--   Candès–Recht, Exact Matrix Completion via Convex Optimization (symmetrization / matrix-moment machinery)

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_expectation_sqrt_le_sqrt_expectation
    {n1 n2 : ℕ} (p : ℝ)
    (F : Finset (Fin n1 × Fin n2) → ℝ) :
    0 ≤ p → p ≤ 1 → (∀ Ω, 0 ≤ F Ω) →
    bernoulliExpectation p (fun Ω => Real.sqrt (F Ω)) ≤
      Real.sqrt (bernoulliExpectation p F) := by sorry
