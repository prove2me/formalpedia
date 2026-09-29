-- Prove2me | Theorems.Thm_mme_stothers_phi233_profile_surplus_of_EHL_order
-- name    : mme_stothers_phi233_profile_surplus_of_EHL_order
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T08:34:06.848985+00:00
-- url     : https://prove2.me/theorems/8e6b3393-144d-429b-b881-eda780e227d0
-- title:
--   Actual-degree profile surplus under ordered Stothers component rates
-- statement:
--   Let $E=E(6,\tau)$, $H=H(6,\tau)$, and $L=L(6,\tau)$ satisfy $0<E<H<L$. For every $0\le V<\operatorname{classValue}(6,\tau,9)$ there is a positive integer $N$ and an exact $(2,3,3)$ profile with $2\alpha+\beta+\gamma+\delta=N$ such that
--   $$V^{2N}D\exp(4000\sqrt{18N+1})<CB.$$
--   Here $D$ is the product of the three actual marginal-fiber counts at a profile address, $C$ is the number of target cyclic addresses, and $B$ is the product of the ten component rates with their profile multiplicities. The surplus is sufficient to absorb the losses of the actual-degree isolation construction. This statement isolates the rate-order assumptions without imposing an exponent ceiling.
-- source:
--   Generalization of the established Stothers 233 profile surplus proof to its rate-order hypotheses.

import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
open MME MME.StothersFourth MME.StothersFourth.Phi233 BigOperators
universe u
set_option autoImplicit false

theorem mme_stothers_phi233_profile_surplus_of_EHL_order
    (tau : ℝ) (hEpos : 0 < MME.StothersFourth.E 6 tau)
    (hEH : MME.StothersFourth.E 6 tau < MME.StothersFourth.H 6 tau)
    (hHL : MME.StothersFourth.H 6 tau < MME.StothersFourth.L 6 tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 9) :
    ∃ N alpha beta gamma delta : ℕ,
      0 < N ∧ 2 * alpha + beta + gamma + delta = N ∧
      ∃ a : ExactProfileAddress N alpha beta gamma delta,
        V ^ (2 * N) *
            (∏ l : Fin 3,
              (Nat.card {b : MarginalAddress N alpha beta gamma delta //
                b.1 l = a.1.1 l} : ℝ)) *
            Real.exp (4000 * Real.sqrt (((18 * N + 1 : ℕ) : ℝ))) <
          ((targetFinset N alpha beta gamma delta).card : ℝ) *
            (∏ r : Fin 10,
          (![MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.E 6 tau ^ (2 : ℕ),
              MME.StothersFourth.L 6 tau ^ (2 : ℕ),
              MME.StothersFourth.L 6 tau ^ (2 : ℕ),
              MME.StothersFourth.E 6 tau ^ (2 : ℕ),
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau] :
                Fin 10 → ℝ) r ^
            MME.StothersFourth.Phi233.profileMultiplicity
              alpha beta gamma delta r) := by sorry
