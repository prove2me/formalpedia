-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_opt_bounds
-- name    : XinGoldbergTBS.Asymptotic.opt_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:22:17.672079+00:00
-- url     : https://prove2.me/theorems/82fe7a5f-1d18-4e94-8a27-d24ee17b1235
-- title:
--   §2.2.1 — $U = C(\pi_{0,0})$ and $g \le \mathrm{OPT}(L) \le U$
-- statement:
--   Let $D'_1, \dots, D'_{L_0+1}$ be i.i.d. copies of $D$. For all $L > L_0 + 1$:
--   1. the TBS policy $\pi_{0,0}$ that never orders from the regular source and expedites up to $0$ has cost
--   $$C(\pi_{0,0}) = U = c\,\mathbb E[D] + \mathbb E\Big[G\Big(-\sum_{i=1}^{L_0+1}D'_i\Big)\Big];$$
--   2. $$g \le \mathrm{OPT}(L) \le U, \qquad g = \inf_{x\in\mathbb R}\mathbb E\Big[G\Big(x - \sum_{i=1}^{L_0+1}D'_i\Big)\Big].$$
--
--   The bound makes $\mathrm{OPT}(L)$ positive and finite, so the ratio $C(\pi_{r^*,S^*})/\mathrm{OPT}(L)$ of Theorem 1 is a well-defined positive real number.
--
--   **Formalization Note** All costs are in $[0,\infty]$; $g$ and $U$ are real constants.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 441, Section 2.2.1

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Section 2.2.1, p. 441: `U = C(π_{0,0}) = c 𝔼[D] + 𝔼[G(-∑_{i=1}^{L₀+1} D'_i)]`, and
`g ≤ OPT(L) ≤ U` for all `L > L₀ + 1`. -/
theorem opt_bounds (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L) :
    tbsCost μ κ L₀ L 0 0 = ENNReal.ofReal (UConst μ κ L₀) ∧
    ENNReal.ofReal (gConst μ κ L₀) ≤ OPT μ κ L₀ L ∧
    OPT μ κ L₀ L ≤ ENNReal.ofReal (UConst μ κ L₀) := by sorry

end XinGoldbergTBS.Asymptotic
