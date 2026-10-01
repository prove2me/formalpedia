-- Prove2me | Theorems.Thm_XuMannorRobust_Quantile_theorem5_quantile_truncated_mean_bounds
-- name    : XuMannorRobust.Quantile.theorem5_quantile_truncated_mean_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:18:43.400507+00:00
-- url     : https://prove2.me/theorems/7eb3bd84-0c1d-441c-85b0-57a1e7f6a3de
-- title:
--   Theorem 5 — quantile-value and truncated-mean generalization bounds for pseudo-robust algorithms
-- statement:
--   Let $\mathcal Z$ be a measurable space, $\mathcal H$ a set of hypotheses and $l : \mathcal H \times \mathcal Z \to [0, M]$ a loss with each $l(h, \cdot)$ measurable. Let the training set $\mathbf s = (s_1, \dots, s_n)$, $n \ge 1$, consist of $n$ i.i.d. draws from a probability measure $\mu$ on $\mathcal Z$, with empirical distribution $\mu_{\mathrm{emp}}$. Let $\mathcal A : \mathcal Z^n \to \mathcal H$ be $(K, \epsilon(\cdot), \hat n(\cdot))$ pseudo robust (Definition 5), let $\beta \in (0,1)$, $\delta > 0$, and
--
--   $$\lambda_0 = \sqrt{\frac{2K \ln 2 + 2 \ln(1/\delta)}{n}}.$$
--
--   Then with probability at least $1 - \delta$ the following holds: if $0 \le \beta - \lambda_0 - \frac{n - \hat n(\mathbf s)}{n}$ and $\beta + \lambda_0 + \frac{n - \hat n(\mathbf s)}{n} \le 1$, then
--
--   1. $\displaystyle \mathcal Q\Big(\mathcal A_{\mathbf s}, \beta - \lambda_0 - \tfrac{n - \hat n(\mathbf s)}{n}, \mu_{\mathrm{emp}}\Big) - \epsilon(\mathbf s) \le \mathcal Q(\mathcal A_{\mathbf s}, \beta, \mu) \le \mathcal Q\Big(\mathcal A_{\mathbf s}, \beta + \lambda_0 + \tfrac{n - \hat n(\mathbf s)}{n}, \mu_{\mathrm{emp}}\Big) + \epsilon(\mathbf s)$;
--   2. $\displaystyle \mathcal T\Big(\mathcal A_{\mathbf s}, \beta - \lambda_0 - \tfrac{n - \hat n(\mathbf s)}{n}, \mu_{\mathrm{emp}}\Big) - \epsilon(\mathbf s) \le \mathcal T(\mathcal A_{\mathbf s}, \beta, \mu) \le \mathcal T\Big(\mathcal A_{\mathbf s}, \beta + \lambda_0 + \tfrac{n - \hat n(\mathbf s)}{n}, \mu_{\mathrm{emp}}\Big) + \epsilon(\mathbf s)$.
--
--   Here $\mathcal Q(h, \beta, \nu)$ and $\mathcal T(h, \beta, \nu)$ are the $\beta$-quantile value and $\beta$-truncated mean of the loss $l(h, z)$, $z \sim \nu$.
--
--   The theorem says that the quantile value and truncated mean of the testing error of a pseudo-robust algorithm are bracketed, up to $\epsilon(\mathbf s)$, by the same functionals of the training errors at slightly shifted levels, so they can be estimated from the training sample.
--
--   **Formalization Note** The level condition involves $\hat n(\mathbf s)$ and so depends on the sample; it is placed inside the high-probability event as the premise of an implication, which is the reading the paper's proof gives (everything holds pointwise on the event $\mathcal E$). "With probability at least $1-\delta$" is encoded as: the outer measure under $\mu^n$ of the set of training sets where the implication fails is at most $\delta$, so no measurability of $\mathbf s \mapsto \mathcal A_{\mathbf s}$ is required. Measurability of each $l(h, \cdot)$ and of the cells of the partition is added (the paper ignores measurability). $\mathcal T$ uses Definition 3 with the misprinted second branch corrected. Levels are real numbers, with $n$ and $\hat n(\mathbf s)$ cast to $\mathbb R$.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 402, Theorem 5 (proof in Appendix C, pp. 415–418)

import Mathlib
import Definitions.Def_XuMannorRobust_Quantile_LossQuantile
import Definitions.Def_XuMannorRobust_Quantile_IsPseudoRobust

open MeasureTheory

namespace XuMannorRobust.Quantile

/-- **Theorem 5** (Xu & Mannor 2012, p. 402; proof in Appendix C, pp. 415–418). Let the loss take
values in `[0, M]` with each `l h` measurable, let `s` consist of `n ≥ 1` i.i.d. draws from the
probability measure `μ`, with empirical distribution `μ_emp`, let `β ∈ (0, 1)`, `δ > 0`,
`λ₀ = √((2K ln 2 + 2 ln(1/δ))/n)` and `r(s) = (n − n̂(s))/n`. If `A` is `(K, ε(·), n̂(·))` pseudo
robust, then with probability at least `1 − δ` the following holds: if
`0 ≤ β − λ₀ − r(s)` and `β + λ₀ + r(s) ≤ 1`, then
(I)  `Q(A_s, β − λ₀ − r(s), μ_emp) − ε(s) ≤ Q(A_s, β, μ) ≤ Q(A_s, β + λ₀ + r(s), μ_emp) + ε(s)`;
(II) `T(A_s, β − λ₀ − r(s), μ_emp) − ε(s) ≤ T(A_s, β, μ) ≤ T(A_s, β + λ₀ + r(s), μ_emp) + ε(s)`.
"With probability at least `1 − δ`" is: the outer measure under `μⁿ` of the set of training sets
where the implication fails is at most `δ`. `T` uses the corrected Definition 3. -/
theorem theorem5_quantile_truncated_mean_bounds {Z H : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (A : (Fin n → Z) → H) (K : ℕ) (ε : (Fin n → Z) → ℝ)
    (nhat : (Fin n → Z) → ℕ) (hA : IsPseudoRobust l A K ε nhat)
    (δ : ℝ) (hδ : 0 < δ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (Measure.pi fun _ : Fin n => μ)
        {s : Fin n → Z | ¬
          ((0 ≤ β - Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                - ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ) ∧
            β + Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                + ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ) ≤ 1) →
          -- (I) quantile value
          ((lossQuantile l (A s)
                (β - Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                  - ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ)) (empiricalMeasure s) - ε s
              ≤ lossQuantile l (A s) β μ ∧
            lossQuantile l (A s) β μ
              ≤ lossQuantile l (A s)
                (β + Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                  + ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ)) (empiricalMeasure s) + ε s) ∧
          -- (II) truncated mean
          (lossTruncatedMean l (A s)
                (β - Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                  - ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ)) (empiricalMeasure s) - ε s
              ≤ lossTruncatedMean l (A s) β μ ∧
            lossTruncatedMean l (A s) β μ
              ≤ lossTruncatedMean l (A s)
                (β + Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                  + ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ)) (empiricalMeasure s) + ε s)))}
      ≤ ENNReal.ofReal δ := by sorry

end XuMannorRobust.Quantile
