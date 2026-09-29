-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_corollary2
-- name    : XinGoldbergTBS.Asymptotic.corollary2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:24:47.630616+00:00
-- url     : https://prove2.me/theorems/6f7763ba-671f-4cc9-9e35-211c51dd2b85
-- title:
--   Corollary 2 — $\mathrm{OPT}(L)$ is at least a discounted sum over the pipeline
-- statement:
--   For all $L_0 \ge 0$, $L > L_0 + 1$, $\alpha \in (0,1)$, and every $(\chi^{*,L}, q^{*,L}, \mathcal I^{*,L}, \{D_i\})$ with properties (i)–(vi) of Theorem 2, where $r_L = \mathbb E[\chi^{*,L}_1]$:
--   $$\begin{aligned}\mathrm{OPT}(L) &\ge c(\mathbb E[D]-r_L) + \frac{1-\alpha}{1-\alpha^L}\sum_{k=1}^{L}\alpha^{k-1}\,\mathbb E\Big[G\Big(\mathcal I^{*,L} + q^{*,L}_1 - \sum_{i=1}^{L_0+1}D_i\Big)\Big]\\ &\ge c(\mathbb E[D]-r_L) + (1-\alpha)\sum_{k=1}^{L-L_0}\alpha^{k-1}\,\mathbb E\Big[G\Big(\mathcal I^{*,L} + \sum_{i=1}^{k-1}(q^{*,L}_i + \chi^{*,L}_i - D_i) + q^{*,L}_k - \sum_{i=k}^{k+L_0}D_i\Big)\Big].\end{aligned}$$
--
--   This introduces the discount factor $\alpha$ of the vanishing-discount argument.
--
--   **Formalization Note** The chain $\mathrm{OPT}(L) \ge A \ge B$ is stated as the two inequalities $A \le \mathrm{OPT}(L)$ and $B \le A$, computed in $[0,\infty]$ (all terms are nonnegative).
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 443, Corollary 2

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Corollary 2, p. 443, for every witness of Theorem 2 (`r_L = 𝔼[χ_1^{*,L}]`); the chain
`OPT(L) ≥ A ≥ B` is stated as `A ≤ OPT(L)` and `B ≤ A`. -/
theorem corollary2 (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal ((1 - α) / (1 - α ^ L)) *
          ∑ k ∈ Finset.range L, ENNReal.ofReal (α ^ k) *
            ∫⁻ ω, ENNReal.ofReal
              (G κ (I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω)) ∂P
      ≤ OPT μ κ L₀ L ∧
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) *
          ∑ k ∈ Finset.range (L - L₀), ENNReal.ofReal (α ^ k) *
            ∫⁻ ω, ENNReal.ofReal (G κ (I ω
                + ∑ i ∈ Finset.range k, (qN L₀ L q ω i + chiN L₀ L χ ω i - D i ω)
                + qN L₀ L q ω k - ∑ i ∈ Finset.range (L₀ + 1), D (k + i) ω)) ∂P
      ≤ ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal ((1 - α) / (1 - α ^ L)) *
          ∑ k ∈ Finset.range L, ENNReal.ofReal (α ^ k) *
            ∫⁻ ω, ENNReal.ofReal
              (G κ (I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω)) ∂P := by sorry

end XinGoldbergTBS.Asymptotic
