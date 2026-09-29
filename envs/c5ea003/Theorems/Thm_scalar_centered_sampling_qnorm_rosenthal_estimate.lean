-- Prove2me | Theorems.Thm_scalar_centered_sampling_qnorm_rosenthal_estimate
-- name    : scalar_centered_sampling_qnorm_rosenthal_estimate
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T23:47:52.474544+00:00
-- url     : https://prove2.me/theorems/aa8e3d3a-bc3f-422a-ad4f-53682695164b
-- statement:
--   The Rosenthal/Bernstein $q$-norm moment estimate for the centered-sampling coefficient statistic on the finite Bernoulli observation measure. The statistic is $\mathrm{Coeff}(\Omega)=\mathrm{matrixEntrySum}(\mathrm{centeredSamplingFluctuation}(\Omega,p,B))=\sum_{i,j} p^{-1}(\mathbf 1[(i,j)\in\Omega]-p)B_{ij}$ with $p=m/(n_1 n_2)$, a sum of independent mean-zero terms (independence of coordinate inclusion under the Bernoulli powerset measure), each with variance $B_{ij}^2(1-p)/p$ and a.s. bound $|B_{ij}|/p$, so $\sigma^2\le\|B\|_F^2/p$ and $L\le\|B\|_\infty/p$. For EVERY exponent $q\ge 1$, the classical Rosenthal (1970) / Bennett-Bernstein moment inequality for a sum of independent centered bounded random variables gives a uniform constant $C$ with $(\mathbb E|\mathrm{Coeff}|^q)^{1/q}\le C(\sqrt{q/p}\cdot\mathrm{frobScale}+(q/p)\cdot\mathrm{entryScale})$, equivalently $\mathbb E|\mathrm{Coeff}|^q\le (C(\sqrt{q/p}\,\mathrm{frobScale}+(q/p)\,\mathrm{entryScale}))^q$, where $\mathrm{entrySupNorm}(B)\le\mathrm{entryScale}$ and $\mathrm{frobeniusNorm}(B)\le\mathrm{frobScale}$. This is the single genuinely analytic core (a Rosenthal/Bernstein moment bound for an independent sum on the bespoke powerset measure; Mathlib has no such tooling). The q-moment Bernstein estimate scalar_centered_sampling_qmoment_bernstein_estimate (and through it the four scalar Bernstein-tail leaves) reduces onto this node by choosing $q=\lceil\beta\log(\max n_1,n_2)\rceil$ and packaging the surplus into $e^{-q}\le(\max n_1,n_2)^{-\beta}$.
-- source:
--   Rosenthal, On the subspaces of L^p spanned by sequences of independent random variables, Israel J. Math. 8 (1970) 273-303; Boucheron-Lugosi-Massart, Concentration Inequalities, OUP 2013, Ch. 15; application to p^{-1}(P_Omega-p) coefficient sums: Candes-Recht 2009, arXiv:0805.4471, Section 6.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem scalar_centered_sampling_qnorm_rosenthal_estimate :
    ∃ C : ℝ, 0 < C ∧
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
        ∀ q : ℕ, 1 ≤ q →
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega => |Coeff Omega| ^ q) ≤
            (C *
                (Real.sqrt
                    ((q : ℝ) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  frobScale +
                  ((q : ℝ) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entryScale)) ^ q := by
  sorry
