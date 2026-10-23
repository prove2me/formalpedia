-- Prove2me | Theorems.Thm_YieldCheapTalk_Truthful_ic_condition_5
-- name    : YieldCheapTalk.Truthful.ic_condition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:43.659439+00:00
-- url     : https://prove2.me/theorems/4524248e-c258-4da7-8424-77f68e8c755d
-- title:
--   §4.2, p. 11, (5) — in a truth-revealing equilibrium Q∗(t, m) = Qʳ(θ_t, a_m), and such an equilibrium exists iff the IC condition (5) holds
-- statement:
--   Assume the standing assumptions of the model. Then:
--
--   1. In every truth-revealing perfect Bayesian equilibrium $(r = \mathrm{id}, Q^*, \beta)$ the buyer orders the symmetric-information quantity:
--   $$Q^*(t, m) = Q^r(\theta_t, a_m) \quad \text{for all } t \in T,\ m \in M .$$
--   2. A truth-revealing equilibrium exists if and only if the IC condition (5) holds: for all $t \ne t'$ in $T$,
--   $$Q^r(\theta_t, a_H)\mu(H\mid t) + Q^r(\theta_t, a_L)\mu(L\mid t) \ge Q^r(\theta_{t'}, a_H)\mu(H\mid t) + Q^r(\theta_{t'}, a_L)\mu(L\mid t).$$
--
--   This converts the equilibrium question into a pair of inequalities between closed-form order quantities: the supplier's incentive to report truthfully is the comparison of the expected orders $\sum_m Q^*(t', m)\mu(m\mid t)$ that each report attracts.
-- source:
--   Lu, Can a Supplier’s Yield Risk Be Truthfully Communicated via Cheap Talk?, author manuscript of 14 July 2024 (MSOM, doi:10.1287/msom.2023.0089), p. 11, §4.2, (4)–(5)

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
theorem ic_condition_5 (M : Model) (hM : M.Standing) :
    (∀ (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ), M.IsPBE id Q beta →
        ∀ t m, Q t m = M.Qr (M.theta t) (M.a m)) ∧
      ((∃ (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ), M.IsPBE id Q beta) ↔
        M.IC5) := by sorry
end YieldCheapTalk.Truthful
