-- Prove2me | Theorems.Thm_mme_stothers_phi134_entropy_rate_identity
-- name    : mme_stothers_phi134_entropy_rate_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:37:29.310143+00:00
-- url     : https://prove2.me/theorems/4dd9ac41-9280-4c82-9581-c20cc245abe3
-- title:
--   Entropy identity for the Davie–Stothers phi_134 profile
-- statement:
--   Let $a,c,\sigma$ be real profile parameters with $a>0$, $c>0$, $c\leq\sigma$, and $\sigma+a\leq1$, and let $L,E,H>0$. The entropy of the three marginal word classes for the symmetric $\phi_{134}$ profile, plus the logarithmic contribution of its eight component values, satisfies
--
--   $$
--   \begin{aligned}
--   &(3-c)\log 2+\operatorname{negMulLog}(\sigma)+\operatorname{negMulLog}(1-\sigma)\\
--   &\quad+\operatorname{negMulLog}(a)+\operatorname{negMulLog}(c)+\operatorname{negMulLog}(1-a-c)\\
--   &\quad+\sigma\log L+\bigl((1-\sigma)+(1-a-c)\bigr)\log E+c\log H\\
--   &=\log\!\left[8\left(\frac L\sigma\right)^\sigma\left(\frac E{1-\sigma}\right)^{1-\sigma}
--   \left(\frac1a\right)^a\left(\frac{H/2}{c}\right)^c\left(\frac E{1-a-c}\right)^{1-a-c}\right].
--   \end{aligned}
--   $$
--
--   The identity remains valid at the allowed boundary $1-a-c=0$ under the standard continuous entropy convention and real-power convention. It is the logarithmic calculation converting the exact marginal multinomial counts and eight fine-component values into the profile-parametric rate in Davie–Stothers Lemma 5.1(iii).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), printed p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib
import Definitions.Def_mme_stothers_fourth_data

open MME Real

set_option autoImplicit false

theorem mme_stothers_phi134_entropy_rate_identity
    (sigma a c L E H : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H) :
    ((3 - c) * Real.log 2 +
        Real.negMulLog sigma + Real.negMulLog (1 - sigma) +
        Real.negMulLog a + Real.negMulLog c +
        Real.negMulLog (1 - a - c)) +
          sigma * Real.log L +
          ((1 - sigma) + (1 - a - c)) * Real.log E +
          c * Real.log H =
      Real.log
        (8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) := by
  sorry
