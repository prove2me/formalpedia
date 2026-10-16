-- Prove2me | Theorems.Thm_YieldPostpone_Preference_Ctil_mem
-- name    : YieldPostpone.Preference.Ctil_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:27.378981+00:00
-- url     : https://prove2.me/theorems/6003eddd-b38b-4ef6-9bfb-7df29d33c9e2
-- title:
--   App. C, proof of Proposition 4, PDF p. 38 — for α ≥ 9/16 the threshold C̃ of (6) lies in (0, c^DR_1)
-- statement:
--   Let $a,b>0$, $\theta\in(0,1)$, $9/16\le\alpha<1$ and $\mu=\alpha(1-\theta)+\theta$. The threshold of (6),
--   $$\tilde C=\frac{a\alpha\big(1-\sqrt{\alpha^2(1-\theta)+\theta}\big)}{b(1+\alpha)},$$
--   satisfies
--   $$0<\tilde C<c^{DR}_1,$$
--   where $c^{DR}_1$ is the first threshold of scenario DR (App. B.4).
--
--   $\tilde C$ is the cost at which the retailer's preference switches from DA to OR in Proposition 2; this statement places the switch inside the first piece of the DR equilibrium.
-- source:
--   Geng, Guo, Xiao, Yang, …, SSRN 3546872 (author version), App. C, proof of Proposition 4, PDF p. 38 (appendix p. 6); (6), PDF p. 37

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting

namespace YieldPostpone.Preference

/-- App. C, proof of Proposition 4, PDF p. 38: for `α ≥ 9/16`, the threshold
`C̃ = aα(1 − √(α²(1 − θ) + θ)) / (b(1 + α))` of (6) lies in `(0, c^DR_1)`. -/
theorem Ctil_mem (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    0 < Ctil P ∧ Ctil P < cDR1 P := by sorry

end YieldPostpone.Preference
