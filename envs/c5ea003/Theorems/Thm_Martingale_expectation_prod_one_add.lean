-- Prove2me | Theorems.Thm_Martingale_expectation_prod_one_add
-- name    : Martingale.expectation_prod_one_add
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T18:37:04.424079+00:00
-- url     : https://prove2.me/theorems/d899fcd1-20dd-4934-81ae-1b4482bc9639
-- title:
--   Step 3 of the martingale CLT: $E\left[\prod_k (1 + i\theta Z_k)\right] = 1$
-- statement:
--   The step where the martingale property does its work. For a bounded martingale difference sequence $\{Z_k\}$ adapted to $\{\mathcal{F}_k\}$ and any real $\theta$,
--
--   $$E\Bigl[\prod_{k<n} \bigl(1 + i\theta Z_k\bigr)\Bigr] = 1 \qquad \text{for every } n.$$
--
--   By induction on $n$: the partial product $\prod_{k<n}(1 + i\theta Z_k)$ is $\mathcal{F}_{n-1}$-measurable and bounded, so it pulls out of the conditional expectation, and
--
--   $$E\bigl[1 + i\theta Z_n \mid \mathcal{F}_{n-1}\bigr] = 1 + i\theta\,E[Z_n \mid \mathcal{F}_{n-1}] = 1 .$$
--
--   Boundedness is what makes the complex product integrable and licenses pulling it out; in the main proof it is supplied by the truncation step.
--
--   **Why this identity is the crux.** For independent summands one proves a central limit theorem by *factoring* the characteristic function $E[e^{i\theta S_n}] = \prod_k E[e^{i\theta X_k}]$, which is unavailable for martingales. McLeish's device is to compare $e^{i\theta S_n}$ with the product $\prod_k (1 + i\theta Z_k)$, which is not a characteristic function but *does* have expectation exactly $1$ for the reason above — the martingale property replaces independence at precisely this point. Writing $e^{i\theta \sum_k Z_k} = J^{(1)}_n J^{(2)}_n$ with $J^{(1)}_n = \prod_k(1 + i\theta Z_k)$, one then shows $J^{(2)}_n \Rightarrow e^{-\theta^2/2}$ and that $J^{(1)}_n(J^{(2)}_n - e^{-\theta^2/2})$ is uniformly integrable and tends to $0$, so that $E[e^{i\theta S_n}] \to e^{-\theta^2/2}\,E[J^{(1)}_n] = e^{-\theta^2/2}$, and Lévy's continuity theorem finishes.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2 and its proof.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem Martingale.expectation_prod_one_add {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (Z : ℕ → Ω → ℝ) (hmeas : ∀ k, Measurable (Z k))
    (hadapt : ∀ k, Measurable[ℱ k] (Z k))
    (hint : ∀ k, Integrable (Z k) P)
    (hmds : ∀ k, P[Z (k + 1) | ℱ k] =ᵐ[P] 0)
    (hcent : ∫ ω, Z 0 ω ∂P = 0)
    (C : ℝ) (hbdd : ∀ k ω, |Z k ω| ≤ C) (θ : ℝ) (n : ℕ) :
    ∫ ω, (∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))) ∂P = 1 := by
  sorry
