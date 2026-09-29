-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma5
-- name    : XinGoldbergTBS.Asymptotic.lemma5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:28:21.93996+00:00
-- url     : https://prove2.me/theorems/ddd806d6-71a1-4689-a8d1-eb87b77351fb
-- title:
--   Lemma 5 — monotonicity, limit, Spitzer identity and tail bound for $M^r_k$
-- statement:
--   For all $r > 0$:
--   1. $\{M^r_k, k\ge1\}$ is nondecreasing and $M^r_\infty = \lim_{k\to\infty}M^r_k$;
--   2. for all $i \ge j \ge 1$, $$M^r_i - M^r_j = \sum_{k=j}^{i-1}k^{-1}\,\mathbb E[\max(0, W^r_k)];$$
--   3. if there exists $\epsilon \in (0, \mathbb E[D])$ with $r \le \mathbb E[D] - \epsilon$, then $M^r_\infty < \infty$ and, for all $n \ge 1$,
--   $$M^r_\infty - M^r_n \le \big(\vartheta_\epsilon(1-\gamma_\epsilon)\big)^{-1}\gamma_\epsilon^n.$$
--
--   Here $W^r_k = \sum_{j=1}^k(r - D_j)$, $M^r_k = \mathbb E[\max_{i\in[0,k-1]}W^r_i]$ and $M^r_\infty = \mathbb E[\sup_{i\ge0}W^r_i]$. The paper omits the proof ("well-known results for generating functions, large deviations, single-server queues").
--
--   **Formalization Note** The identity in 2 and the bound in 3 are stated additively in $[0,\infty]$ ($M^r_i = M^r_j + \sum\dots$ and $M^r_\infty \le M^r_n + \dots$). The $M^r_j$ are finite, so this is equivalent to the difference form. In 3, $\vartheta_\epsilon^{-1}$ uses $1/\infty = 0$ (computed in $[0,\infty]$).
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 444, Lemma 5

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_RandomWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Lemma 5, p. 444: for `r > 0`, `M^r_k` is nondecreasing in `k ≥ 1`, `M^r_∞ = lim_k M^r_k`,
`M^r_i - M^r_j = ∑_{k=j}^{i-1} k^{-1} 𝔼[max(0, W^r_k)]` for `i ≥ j ≥ 1` (stated additively), and if
`r ≤ 𝔼[D] - ϵ` for some `ϵ ∈ (0, 𝔼[D])` then `M^r_∞ < ∞` and
`M^r_∞ - M^r_n ≤ (ϑ_ϵ (1 - γ_ϵ))^{-1} γ_ϵ^n` for `n ≥ 1` (stated additively, `1/∞ = 0`). -/
theorem lemma5 (μ : DemandLaw) (r : ℝ) (hr : 0 < r) :
    (∀ i j : ℕ, 1 ≤ j → j ≤ i → M μ r j ≤ M μ r i) ∧
    Tendsto (fun k => M μ r k) atTop (nhds (Minf μ r)) ∧
    (∀ i j : ℕ, 1 ≤ j → j ≤ i →
      M μ r i = M μ r j + ∑ k ∈ Finset.Ico j i,
        ((k : ℝ≥0∞))⁻¹ * ∫⁻ d, ENNReal.ofReal (W r d k) ∂pathLaw μ) ∧
    (∀ ϵ : ℝ, 0 < ϵ → ϵ < μ.mean → r ≤ μ.mean - ϵ →
      Minf μ r < ⊤ ∧
      ∀ n : ℕ, 1 ≤ n →
        Minf μ r ≤ M μ r n +
          (vartheta μ ϵ * ENNReal.ofReal (1 - gamma μ ϵ))⁻¹ * ENNReal.ofReal (gamma μ ϵ) ^ n) := by sorry

end XinGoldbergTBS.Asymptotic
