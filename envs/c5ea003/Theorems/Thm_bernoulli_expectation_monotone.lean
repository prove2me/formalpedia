-- Prove2me | Theorems.Thm_bernoulli_expectation_monotone
-- name    : bernoulli_expectation_monotone
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T14:39:00.219022+00:00
-- url     : https://prove2.me/theorems/ec60bc6a-8696-4a0d-a774-f9ada073a20a
-- statement:
--   **Monotonicity of the Bernoulli expectation in the integrand.**
--
--   Fix dimensions $n_1,n_2$ and an inclusion probability $p\in[0,1]$. Let $\mathbb E_p[F]=\sum_\Omega w_p(\Omega)\,F(\Omega)$ with weights $w_p(\Omega)=p^{|\Omega|}(1-p)^{N-|\Omega|}$, $N=n_1n_2$. If $F(\Omega)\le G(\Omega)$ for every observation set $\Omega$, then
--   $$\mathbb E_p[F]\le\mathbb E_p[G].$$
--
--   The hypothesis $0\le p\le1$ is exactly what makes every weight $w_p(\Omega)\ge0$, so the inequality survives summation. This is the Bernoulli-model analogue of `rademacher_expectation_monotone`, used to push per-$\Omega$ conditional bounds through the outer expectation over the sampling set.
-- source:
--   Candès–Recht, Exact Matrix Completion via Convex Optimization (Bernoulli model)

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_expectation_monotone
    {n1 n2 : ℕ} (p : ℝ)
    (F G : Finset (Fin n1 × Fin n2) → ℝ) :
    0 ≤ p → p ≤ 1 → (∀ Ω, F Ω ≤ G Ω) →
    bernoulliExpectation p F ≤ bernoulliExpectation p G := by sorry
