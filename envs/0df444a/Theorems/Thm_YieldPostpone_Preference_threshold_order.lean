-- Prove2me | Theorems.Thm_YieldPostpone_Preference_threshold_order
-- name    : YieldPostpone.Preference.threshold_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:29.901082+00:00
-- url     : https://prove2.me/theorems/ba49072b-f5d5-459e-a5ac-09589f2bc4e8
-- title:
--   App. C, proof of Propositions 1 and 2, PDF p. 38 — for α ≥ 9/16, c^OR < 0 and c^DR_1 < c^DR_2 < c^DA
-- statement:
--   Let $a,b>0$, $\theta\in(0,1)$, $9/16\le\alpha<1$ and $\mu=\alpha(1-\theta)+\theta$. With the thresholds $c^{OR}$ (App. B.2), $c^{DA}$ (App. B.3) and $c^{DR}_1,c^{DR}_2$ (App. B.4),
--   $$c^{OR}<0\qquad\text{and}\qquad c^{DR}_1<c^{DR}_2<c^{DA}.$$
--
--   The first inequality means only the second piece of the OR equilibrium is relevant; the chain fixes which pieces of the DA and DR equilibria are compared on each cost interval in Proposition 2.
--
--   **Formalization Note** The same sentence of the proof also orders $c^{OA}_1<c^{OA}_2<c^{DR}_2$; that part concerns scenario OA (Proposition 1) and is not posed here.
-- source:
--   Geng, Guo, Xiao, Yang, …, SSRN 3546872 (author version), App. C, proof of Propositions 1 and 2, PDF p. 38 (appendix p. 6); also p. 13

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting

namespace YieldPostpone.Preference

/-- App. C, proof of Propositions 1 and 2, PDF p. 38: for `α ≥ 9/16`, `c^OR < 0` and
`c^DR_1 < c^DR_2 < c^DA`. -/
theorem threshold_order (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    cOR P < 0 ∧ cDR1 P < cDR2 P ∧ cDR2 P < cDA P := by sorry

end YieldPostpone.Preference
