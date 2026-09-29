-- Prove2me | Theorems.Thm_mme_CW_auxiliary_mono
-- name    : mme_CW_auxiliary_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T23:34:48.151822+00:00
-- url     : https://prove2.me/theorems/4fd7f9fb-da18-4c5b-8391-59c032c4f60b
-- title:
--   The q=6 auxiliary expression is monotone in tau
-- statement:
--   Fix the exact $q=6$ certificate parameters $a,b,c,d$ from the Coppersmith--Winograd endpoint. If $\tau_1\le\tau_2$, then $$\operatorname{auxiliaryRHS}(6,\tau_1,a,b,c,d)\le\operatorname{auxiliaryRHS}(6,\tau_2,a,b,c,d).$$ All denominator factors are independent of $\tau$. In the numerator, the bases $12$ and $38$ exceed one, while $6^{3\tau}$ and hence $4\,6^{3\tau}(6^{3\tau}+2)$ are increasing; all parameter coefficients and the outer exponent $d$ are positive. This monotonicity connects the strict rational endpoint certificate to the Section 8 upper bound.
-- source:
--   Direct monotonicity consequence of the normalized auxiliary expression in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 269 (PDF p. 19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
open MME

theorem mme_CW_auxiliary_mono (tau₁ tau₂ : ℝ) (hτ : tau₁ ≤ tau₂) :
    auxiliaryRHS 6 tau₁ cw2376_a cw2376_b cw2376_c cw2376_d ≤
      auxiliaryRHS 6 tau₂ cw2376_a cw2376_b cw2376_c cw2376_d := by sorry
