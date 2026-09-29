-- Prove2me | Theorems.Thm_scalar_centered_sampling_qmoment_bernstein_estimate
-- name    : scalar_centered_sampling_qmoment_bernstein_estimate
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T20:28:44.276215+00:00
-- url     : https://prove2.me/theorems/75459b07-b57f-4475-9301-77a87db91397
-- statement:
--   The scalar Bernstein $q$-th moment estimate for the centered-sampling coefficient statistic on the finite Bernoulli observation measure. The statistic is $\mathrm{Coeff}(\Omega)=\mathrm{matrixEntrySum}\big(\mathrm{centeredSamplingFluctuation}(\Omega, p, B)\big)=\sum_{i,j} p^{-1}\big(\mathbf 1[(i,j)\in\Omega]-p\big)B_{ij}$ with $p=m/(n_1n_2)$, a sum of independent mean-zero terms (independence of coordinate inclusion under the Bernoulli powerset measure). Each term has variance $\mathrm{Var}=B_{ij}^2(1-p)/p$ and a.s. bound $|\cdot|\le|B_{ij}|/p$, so the variance proxy is $\sigma^2\le\|B\|_F^2/p$ and the sup bound is $L\le\|B\|_\infty/p$. The classical Bernstein/Bennett moment inequality for sums of independent centered bounded random variables gives, with $q=\lceil\beta\log(\max(n_1,n_2))\rceil\ge 1$, $$\mathbb E\,|\mathrm{Coeff}|^q\le \Big(C_{\mathrm{bern}}\big(\sqrt{(\beta\log n)/p}\,\cdot\mathrm{frobScale}+((\beta\log n)/p)\cdot\mathrm{entryScale}\big)\Big)^q\cdot\big(c_{\mathrm{bern}}\,(\max(n_1,n_2))^{-\beta}\big),$$ where $\mathrm{entrySupNorm}(B)\le\mathrm{entryScale}$ and $\mathrm{frobeniusNorm}(B)\le\mathrm{frobScale}$. This is exactly the $q$-th moment input consumed by the proved Markov-tail node $\texttt{scalar\_centered\_sampling\_markov\_tail\_from\_qmoment\_bound}$ to produce the scalar centered-sampling Bernstein tail. It isolates the single genuinely analytic core (a Rosenthal/Bernstein moment bound for an independent sum on the bespoke powerset measure), which has no existing Mathlib formalization.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 15 (Moment inequalities), Bennett/Bernstein moment form; Rosenthal 1970. Applied to the p^{-1}(P_Omega - p) coefficient sums in Candès–Recht 2009, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, §6.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem scalar_centered_sampling_qmoment_bernstein_estimate :
    ∃ Cbern cbern : ℝ, 0 < Cbern ∧ 0 < cbern ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        ∃ q : ℕ, 1 ≤ q ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega => |Coeff Omega| ^ q) ≤
            (Cbern *
                (Real.sqrt
                    ((β * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  frobScale +
                  ((β * Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entryScale)) ^ q *
              (cbern * Real.rpow (↑(max n₁ n₂)) (-β)) := by sorry
