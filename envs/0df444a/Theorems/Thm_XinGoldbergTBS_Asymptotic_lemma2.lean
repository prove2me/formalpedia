-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma2
-- name    : XinGoldbergTBS.Asymptotic.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:25:41.070255+00:00
-- url     : https://prove2.me/theorems/27c8ff4f-2f85-45d6-b5c7-484f425878f1
-- title:
--   Lemma 2 — $\mathrm{OPT}(L) \ge c(\mathbb E[D]-r_L) + (1-\alpha)V_\alpha^{L-L_0}(r_L,-\infty)$
-- statement:
--   For all $L_0 \ge 0$, $L > L_0 + 1$, $\alpha \in (0,1)$, and every witness of Theorem 2 with $r_L = \mathbb E[\chi^{*,L}_1]$:
--   $$\mathrm{OPT}(L) \ge c(\mathbb E[D] - r_L) + (1-\alpha)\,V_\alpha^{L-L_0}(r_L, -\infty), \tag{7}$$
--   where $V^n_\alpha(r,-\infty) = \inf_{x\in\mathbb R}V^n_\alpha(r,x)$ is the optimal $n$-period discounted cost of the single-source backlog problem with demand $D - r$, lead time $L_0$ and zero ordering cost.
--
--   This relates the dual-sourcing optimum to a single-source problem, via the conditional Jensen inequality.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 443, Lemma 2, Eq. (7)

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Lemma 2, p. 443 (eq. (7)), for every witness of Theorem 2:
`OPT(L) ≥ c(𝔼[D] - r_L) + (1 - α) V_α^{L-L₀}(r_L, -∞)`. -/
theorem lemma2 (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) * VnNegInf μ κ L₀ α (L - L₀) (rL P L₀ L χ)
      ≤ OPT μ κ L₀ L := by sorry

end XinGoldbergTBS.Asymptotic
