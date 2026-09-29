-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_tbs_cost_formula
-- name    : XinGoldbergTBS.Asymptotic.tbs_cost_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:23:44.168619+00:00
-- url     : https://prove2.me/theorems/0148e867-2f96-4f46-8fd4-44c78a41e3c5
-- title:
--   Eq. (3) — $C(\pi_{r,S}) = c(\mathbb E[D]-r) + \mathbb E[G(I^r_\infty + S - \sum_{i=1}^{L_0+1}D'_i)]$
-- statement:
--   Let $I^r_\infty = \sup_{j\ge0}\big(jr - \sum_{i=1}^j D_i\big)$, independent of the i.i.d. copies $D'_1, \dots, D'_{L_0+1}$ of $D$. For $L > L_0 + 1$, every $r \in [0, \mathbb E[D])$ and every $S \in \mathbb R$,
--   $$C(\pi_{r,S}) = c(\mathbb E[D] - r) + \mathbb E\Big[G\Big(I^r_\infty + S - \sum_{i=1}^{L_0+1} D'_i\Big)\Big]. \tag{3}$$
--
--   This formula, which the paper takes from Janakiraman, Seshadri and Shanthikumar (JSS), reduces the cost of a TBS policy to a newsvendor-type expression and is the starting point of the upper bound in the proof of Theorem 1.
--
--   **Formalization Note** The paper states (3) without a range for $r$; it is stated here for $0 \le r \le \mathbb E[D]$, the range of the TBS parameter $r$ over which the paper optimizes (p. 441; TBS orders are nonnegative). For $r < \mathbb E[D]$ the supremum $I^r_\infty$ is finite almost surely; at $r = \mathbb E[D]$ it is $+\infty$ almost surely and both sides equal $+\infty$. $I^r_\infty$ is the $[0,\infty]$-valued $Z^r_\infty$, and the integrand is $+\infty$ where $I^r_\infty = +\infty$.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 440, Eq. (3) (from JSS)

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_RandomWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Eq. (3), p. 440 (from JSS): with `I^r_∞ = sup_{j ≥ 0}(jr - ∑_{i=1}^j D_i)` independent of
`D'_1, …, D'_{L₀+1}`, `C(π_{r,S}) = c(𝔼[D] - r) + 𝔼[G(I^r_∞ + S - ∑_{i=1}^{L₀+1} D'_i)]`, for
`r ∈ [0, 𝔼[D]]` (the TBS parameters of p. 441) and `S ∈ ℝ`. The integrand is `+∞` where
`I^r_∞ = +∞` (at `r = 𝔼[D]` this happens almost surely, and both sides are `+∞`). -/
theorem tbs_cost_formula (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    (r S : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ μ.mean) :
    tbsCost μ κ L₀ L r S =
      ENNReal.ofReal (κ.c * (μ.mean - r)) +
        ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
          (if Zinf r p.1 = ⊤ then ⊤
            else ENNReal.ofReal (G κ ((Zinf r p.1).toReal + S - ∑ i, p.2 i)))
          ∂((pathLaw μ).prod (sumLaw μ L₀)) := by sorry

end XinGoldbergTBS.Asymptotic
