-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_proposition_5
-- name    : ZCDPtoGDP.Sharp.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:56:13.594071+00:00
-- url     : https://prove2.me/theorems/9a53eecb-d534-4e69-91f1-389aad0a08f4
-- title:
--   Proposition 5 — randomized response $\mathrm{RR}_t$ is tightly $t\tanh(t/2)$-zCDP and tightly $2\Phi^{-1}(\sigma(t))$-GDP
-- statement:
--   For $t\ge0$ let $\mathrm{RR}_t$ be binary randomized response on $\{0,1\}$ with neighbouring relation $0\sim1$: $\mathrm{RR}_t(0)=\mathrm{Bern}(\sigma(-t))$ and $\mathrm{RR}_t(1)=\mathrm{Bern}(\sigma(t))$. Then, for every $t\ge0$:
--
--   1. $\mathrm{RR}_t$ is $t\tanh(t/2)$-zCDP;
--   2. $\mathrm{RR}_t$ is not $\rho'$-zCDP for any $\rho'<t\tanh(t/2)$;
--   3. $\mathrm{RR}_t$ is $2\Phi^{-1}(\sigma(t))$-GDP;
--   4. $\mathrm{RR}_t$ is not $\mu'$-GDP for any $\mu'<2\Phi^{-1}(\sigma(t))$.
--
--   So both parameters are exact. Randomized response is the mechanism that attains the sharp conversion of Theorem 6.
--
--   Differences from the source:
--   - reading: RR_t with its (implicit) neighbouring relation → the relation 0 ∼ 1, i.e. x ∼ x′ iff x ≠ x′; reason: the source leaves it implicit; the usual Hamming-distance-one adjacency from §2 (p. 4) specializes on a single bit to x ≠ x′; diagonal pairs, if included, impose no additional constraint at the nonnegative privacy budgets in scope
--   - encoding: input and output space {0,1} → Bool with true = 1; reason: Lean convention; same instances
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, Proposition 5, p. 5 (cited from [Ste24, HM26] and [AR24, Lemma 2])

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-- Proposition 5 (Exact privacy parameters of randomized response), p. 5: for every
`t ≥ 0`, `RR_t` is `t tanh(t/2)`-zCDP and `2Φ⁻¹(σ(t))`-GDP, and no smaller parameter is
valid in either framework. -/
theorem proposition_5 (t : ℝ) (ht : 0 ≤ t) :
    IsZCDP rrAdj (randResp t) (t * Real.tanh (t / 2)) ∧
    (∀ ρ' : ℝ, ρ' < t * Real.tanh (t / 2) → ¬ IsZCDP rrAdj (randResp t) ρ') ∧
    IsGDP rrAdj (randResp t) (2 * stdNormalQuantile (Real.sigmoid t)) ∧
    (∀ μ' : ℝ, μ' < 2 * stdNormalQuantile (Real.sigmoid t) →
      ¬ IsGDP rrAdj (randResp t) μ') := by sorry

end ZCDPtoGDP.Sharp
