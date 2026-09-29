-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_tbs_asymptotically_optimal
-- name    : XinGoldbergTBS.Asymptotic.tbs_asymptotically_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:30:41.430731+00:00
-- url     : https://prove2.me/theorems/657f1a18-7745-4168-9b66-936562b88aed
-- title:
--   Theorem 1 — $C(\pi_{r^*,S^*})/\mathrm{OPT}(L) < 1 + \epsilon$ for $L > \epsilon_0^{-2} + Y_0\epsilon^{-2}$
-- statement:
--   For all $L_0 \ge 0$, $\epsilon \in (0,1)$ and regular lead times
--   $$L > \epsilon_0^{-2} + Y_0\,\epsilon^{-2},$$
--   the best tailored base-surge policy is within a factor $1 + \epsilon$ of optimal:
--   $$\frac{C(\pi_{r^*,S^*})}{\mathrm{OPT}(L)} < 1 + \epsilon$$
--   for every best TBS pair $(r^*, S^*)$. In addition, some TBS policy $\pi_{r,S}$ with $0 \le r \le \mathbb E[D]$ satisfies the same bound.
--
--   Here $\mathrm{OPT}(L)$ is the optimal long-run average cost over all admissible policies of the dual-sourcing backlog system, and $\epsilon_0$, $Y_0$ are the explicit constants of Section 2.2.1, which depend only on the demand distribution, $L_0$, $b$, $h$ and $c$, not on $L$. As $L \to \infty$ the ratio tends to $1$ (Corollary 1), with an explicit inverse-polynomial rate.
--
--   **Formalization Note** The ratio is stated as $C(\pi_{r^*,S^*}) < (1+\epsilon)\,\mathrm{OPT}(L)$ in $[0,\infty]$. Because $0 < g \le \mathrm{OPT}(L) \le U < \infty$ (Section 2.2.1), this is equivalent to the ratio form. The paper asserts, citing JSS, that a best pair exists; the first conjunct (existence of a good TBS policy with $r \in [0,\mathbb E[D]]$) keeps the statement non-vacuous without relying on that. $L > L_0 + 1$ follows from the threshold. TBS policies are members of the admissible class, so $C(\pi_{r,S}) \ge \mathrm{OPT}(L)$.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 441, Theorem 1

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Theorem 1, p. 441: for all `L₀ ≥ 0`, `ϵ ∈ (0, 1)` and `L > ϵ₀^{-2} + Y₀ ϵ^{-2}`,
`C(π_{r*,S*}) / OPT(L) < 1 + ϵ`, stated as `C(π_{r*,S*}) < (1 + ϵ) OPT(L)` in `ℝ≥0∞`, for every best
TBS pair `(r*, S*)`, together with the existence of a TBS policy with `0 ≤ r ≤ 𝔼[D]` meeting the
same bound. -/
theorem tbs_asymptotically_optimal (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (ϵ : ℝ)
    (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hL : (eps0 μ κ L₀ ^ 2)⁻¹ + Y0 μ κ L₀ * (ϵ ^ 2)⁻¹ < (L : ℝ)) :
    (∃ r ∈ Set.Icc 0 μ.mean, ∃ S : ℝ,
      tbsCost μ κ L₀ L r S < ENNReal.ofReal (1 + ϵ) * OPT μ κ L₀ L) ∧
    ∀ r S : ℝ, IsBestTBS μ κ L₀ L r S →
      tbsCost μ κ L₀ L r S < ENNReal.ofReal (1 + ϵ) * OPT μ κ L₀ L := by sorry

end XinGoldbergTBS.Asymptotic
