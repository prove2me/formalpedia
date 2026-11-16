-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_Supplement_theorem_13
-- name    : ZCDPtoGDP.Sharp.Supplement.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:11:34.534205+00:00
-- url     : https://prove2.me/theorems/c03d7530-30fc-4475-8a23-df1f6fd7f3a8
-- title:
--   Theorem 13 — Sharp bounded-range and logistic DP conversion
-- statement:
--   Fix $\varepsilon\ge0$ and define
--   $$\mu_{\mathrm{BR}}(\varepsilon)=2\Phi^{-1}(\sigma(\varepsilon/2)).$$
--   For arbitrary input and output measurable spaces, every Markov mechanism with a symmetric neighboring relation satisfies both implications:
--   $$\varepsilon\text{-BR}\Longrightarrow\mu_{\mathrm{BR}}(\varepsilon)\text{-GDP},\qquad \varepsilon\text{-logistic DP}\Longrightarrow\mu_{\mathrm{BR}}(\varepsilon)\text{-GDP}.$$
--   Randomized response $\mathrm{RR}_{\varepsilon/2}$, with the published neighboring relation on its two input bits, is both $\varepsilon$-BR and $\varepsilon$-logistic DP, is $\mu_{\mathrm{BR}}(\varepsilon)$-GDP, and fails $\mu'$-GDP for every $\mu'<\mu_{\mathrm{BR}}(\varepsilon)$.
--
--   Thus the same mechanism witnesses optimality for both classes, including at zero budget. Bounded range means width $\varepsilon$ of the log-likelihood ratio with pair-dependent interval location; it does not require the interval to be centered. Logistic DP and GDP both quantify over the full closed testing interval and all randomized tests.
--
--   Differences from the source:
--   - encoding: log(dQ/dP) P-almost surely for mutually absolutely continuous probability laws → the RN derivative is explicitly finite and positive almost surely before log of toReal; reason: these properties follow from the probability laws and mutual absolute continuity and exclude no source instance
--   - encoding: randomized response on {0,1} with parameter ε/2 → the published randResp on Bool and rrAdj x x′ iff x ≠ x′; reason: this reuses exactly the source two-point mechanism and its neighboring relation
-- source:
--   Yu-Wei Chen, Aaradhya Pandey, Jordan Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), Theorem 13, p. 8; proof pp. 22–23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Supplement_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Supplement_Conversions

open MeasureTheory ProbabilityTheory

namespace ZCDPtoGDP.Sharp.Supplement

/-- Theorem 13, p. 8 (proof pp. 22–23): both universal conversions and
their common randomized-response witness, including budget zero.
The spaces are arbitrary measurable spaces, as in §2, p. 4. -/
theorem theorem_13 (ε : ℝ) (hε : 0 ≤ ε) :
    (∀ {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
      (adj : X → X → Prop) (hadj : Symmetric adj)
      (M : Kernel X Ω) [IsMarkovKernel M],
      (IsBR adj M ε → IsGDP adj M (muBR ε)) ∧
      (IsLogisticDP adj M ε → IsGDP adj M (muBR ε))) ∧
    IsBR rrAdj (randResp (ε / 2)) ε ∧
    IsLogisticDP rrAdj (randResp (ε / 2)) ε ∧
    IsGDP rrAdj (randResp (ε / 2)) (muBR ε) ∧
    ∀ μ' : ℝ, μ' < muBR ε → ¬ IsGDP rrAdj (randResp (ε / 2)) μ' := by sorry

end ZCDPtoGDP.Sharp.Supplement
