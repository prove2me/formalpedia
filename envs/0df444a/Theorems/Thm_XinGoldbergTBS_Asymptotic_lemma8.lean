-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma8
-- name    : XinGoldbergTBS.Asymptotic.lemma8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:28:52.534632+00:00
-- url     : https://prove2.me/theorems/f7d16301-9bc7-494c-926d-cb8b45a0d8bd
-- title:
--   Lemma 8 — $M^r_i - M^r_j$ grows like $\sqrt i - \sqrt j$ when $r$ is close to $\mathbb E[D]$
-- statement:
--   If there exists $\epsilon \in [0, \mathbb E[D] - Q_0]$ such that $r \in (\mathbb E[D] - \epsilon, \mathbb E[D]]$, then for all integers $i \ge j$ in $\big[400\hat p_0^{-2}, (\hat p_0\eta_0\epsilon^{-1})^2\big]$,
--   $$M^r_i - M^r_j \ge \tfrac15\hat p_0\eta_0\big(i^{1/2} - j^{1/2}\big) - (i-j)\epsilon - 2\eta_0\Big(\log\frac{i}{j} + 2\Big).$$
--
--   This is the lower estimate used to show that $r_L$ cannot be too close to $\mathbb E[D]$ (Corollary 4).
--
--   **Formalization Note** When $\epsilon = 0$, the upper end $(\hat p_0\eta_0\epsilon^{-1})^2$ is read as $+\infty$ (no upper restriction). The $M^r_k$ are finite for finite $k$ and are compared as real numbers.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 449, Appendix A.3, Lemma 8

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_RandomWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Lemma 8, p. 449: if `r ∈ (𝔼[D] - ϵ, 𝔼[D]]` for some `ϵ ∈ [0, 𝔼[D] - Q₀]`, then for all
integers `i ≥ j` in `[400 p̂₀^{-2}, (p̂₀ η₀ ϵ^{-1})²]` (no upper limit when `ϵ = 0`),
`M^r_i - M^r_j ≥ (1/5) p̂₀ η₀ (i^{1/2} - j^{1/2}) - (i - j) ϵ - 2 η₀ (log(i/j) + 2)`. -/
theorem lemma8 (μ : DemandLaw) (ϵ : ℝ) (hϵ0 : 0 ≤ ϵ) (hϵ : ϵ ≤ μ.mean - Q0 μ)
    (r : ℝ) (hr1 : μ.mean - ϵ < r) (hr2 : r ≤ μ.mean) (i j : ℕ)
    (hj : 400 * (p0hat μ ^ 2)⁻¹ ≤ (j : ℝ))
    (hi : 0 < ϵ → (i : ℝ) ≤ (p0hat μ * eta0 μ * ϵ⁻¹) ^ 2) (hji : j ≤ i) :
    (1 / 5) * p0hat μ * eta0 μ * (Real.sqrt i - Real.sqrt j) - ((i : ℝ) - j) * ϵ
        - 2 * eta0 μ * (Real.log ((i : ℝ) / j) + 2)
      ≤ (M μ r i).toReal - (M μ r j).toReal := by sorry

end XinGoldbergTBS.Asymptotic
