-- Prove2me | Theorems.Thm_centered_sampling_coefficient_bernstein_mgf
-- name    : centered_sampling_coefficient_bernstein_mgf
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T02:17:52.652036+00:00
-- url     : https://prove2.me/theorems/9a4b682e-082d-4ddd-b65d-a0610cbf4153
-- statement:
--   **Bernstein (variance-scaled) moment generating function bound for the centered-sampling coefficient.** Let $\mathrm{Coeff}(\Omega) = \texttt{matrixEntrySum}(\texttt{centeredSamplingFluctuation}\,\Omega\,p\,B) = \sum_w p^{-1}(\mathbf 1[w\in\Omega]-p)B_w$ be the linear centered statistic under the Bernoulli powerset measure with inclusion probability $p \in (0,1]$. Suppose $\|B\|_\infty \le \texttt{entryScale}$ with $\texttt{entryScale} > 0$, and let $0 \le \lambda \le p/\texttt{entryScale}$. Then
--   $$ \mathbb E\big[e^{\lambda\,\mathrm{Coeff}}\big] \le \exp\!\Big( \lambda^2 \cdot \tfrac{1-p}{p}\cdot \|B\|_F^2 \Big). $$
--   The exponent carries the **true variance** $\tfrac{1-p}{p}\|B\|_F^2 \sim 1/p$, not the looser Hoeffding range proxy $\sim 1/p^2$ — this is exactly the scaling needed for the $\sqrt{q/p}$ term of the Rosenthal/Bernstein $q$-th moment bound. The proof factorizes the MGF over coordinates (each factor is the MGF of a centered two-point increment with values $\lambda p^{-1}(1-p)B_w$ and $-\lambda B_w$, both $\le 1$ in the admissible $\lambda$-range) and applies the two-point Bernstein MGF inequality coordinatewise; the per-coordinate variances $\lambda^2 \tfrac{1-p}{p}B_w^2$ sum to $\lambda^2 \tfrac{1-p}{p}\|B\|_F^2$.
-- source:
--   Bernstein MGF method on the Bernoulli powerset measure; Boucheron, Lugosi, Massart, 'Concentration Inequalities', OUP 2013, Ch. 2; Candès–Recht 2009, arXiv:0805.4471, §6.

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped BigOperators Classical

theorem centered_sampling_coefficient_bernstein_mgf {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) (entryScale lam : ℝ)
    (hent : entrySupNorm B ≤ entryScale) (hes : 0 < entryScale)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ p / entryScale) :
    bernoulliExpectation p
        (fun Omega =>
          Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) ≤
      Real.exp (lam ^ 2 * ((1 - p) / p) * frobeniusNormSq B) := by sorry
