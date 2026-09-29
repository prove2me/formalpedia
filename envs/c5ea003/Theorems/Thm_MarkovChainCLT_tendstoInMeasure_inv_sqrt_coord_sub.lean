-- Prove2me | Theorems.Thm_MarkovChainCLT_tendstoInMeasure_inv_sqrt_coord_sub
-- name    : MarkovChainCLT.tendstoInMeasure_inv_sqrt_coord_sub
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T18:04:14.295814+00:00
-- url     : https://prove2.me/theorems/2d8fb2b4-5f4d-467a-bdbd-f05671eeebfd
-- title:
--   A fixed $L^1$ boundary term scaled by $n^{-1/2}$ vanishes in probability
-- statement:
--   Let $X$ be a Harris ergodic chain run from $\pi$ and let $h \in L^1(\pi)$. Then
--
--   $$\frac{h(X_0) - h(X_n)}{\sqrt n} \;\longrightarrow\; 0 \qquad \text{in probability.}$$
--
--   Every coordinate of the stationary chain has law $\pi$, so $h(X_0)$ and $h(X_n)$ have the *same* fixed law for all $n$; in particular $E|h(X_0) - h(X_n)| \le 2\,E_\pi|h|$ is a constant. Markov's inequality then gives, for $\varepsilon > 0$,
--
--   $$\Pr\left(\left|\frac{h(X_0)-h(X_n)}{\sqrt n}\right| \ge \varepsilon\right)
--   \;\le\; \frac{2\,E_\pi|h|}{\varepsilon\sqrt n} \;\longrightarrow\; 0 .$$
--
--   No independence, mixing or ergodicity beyond stationarity of the marginals is used — only that the law of $h(X_n)$ does not drift with $n$, so the boundary term is bounded in probability while the normalisation $\sqrt n$ grows.
--
--   This is the step that discards the telescoping remainder in the martingale-approximation proof of the Markov chain CLT. After solving the Poisson equation one has $\sum_{i<n}\bar f(X_{i+1}) = M_n + (P\hat g)(X_0) - (P\hat g)(X_n)$; dividing by $\sqrt n$, this lemma applied to $h = P\hat g$ shows the difference between the normalised sum and the normalised martingale tends to $0$ in probability, so Slutsky's theorem transfers the martingale central limit theorem to the sample average.
-- source:
--   L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728, Theorem 5 (the uniformly ergodic CLT); the martingale-approximation proof is M. I. Gordin (1969) / C. Kipnis and S. R. S. Varadhan, "Central limit theorem for additive functionals of reversible Markov processes", Comm. Math. Phys. 104 (1986) 1-19, Corollary 1.5. Cited as the route to Corollary 5 in G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Remark 8 and Section 4.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.tendstoInMeasure_inv_sqrt_coord_sub {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (h : X → ℝ) (hhm : Measurable h) (hh : Integrable h π) :
    TendstoInMeasure (chainMeasure P π)
      (fun (n : ℕ) (ω : ℕ → X) => (Real.sqrt n)⁻¹ * (h (ω 0) - h (ω n))) atTop 0 := by sorry
