-- Prove2me | Theorems.Thm_mme_stothers_phi233_profile_surplus_of_E_lt_L
-- name    : mme_stothers_phi233_profile_surplus_of_E_lt_L
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T08:39:08.841131+00:00
-- url     : https://prove2.me/theorems/5995a069-5b75-47ae-a20d-b1f7c59c84f0
-- title:
--   Actual-degree Stothers 233 profile surplus without an upper exponent bound
-- statement:
--   Let $E=E(6,\tau)>0$, $H=H(6,\tau)>0$, and suppose $E<L(6,\tau)$. For every $0\le V<\operatorname{classValue}(6,\tau,9)$ there is a positive integer $N$ and an exact profile with $2\alpha+\beta+\gamma+\delta=N$ such that
--   $$V^{2N}D\exp(4000\sqrt{18N+1})<CB.$$
--   Here $D$ is the product of the three actual marginal-fiber counts at a profile address, $C$ counts target cyclic addresses, and $B$ is the product of the ten component rates with their profile multiplicities. This supplies the surplus required for actual-degree isolation without assuming $H<L$ or an upper bound on the exponent.
-- source:
--   Generalization of the established Stothers 233 entropy and actual-degree isolation formalization.

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
open MME MME.StothersFourth MME.StothersFourth.Phi233 BigOperators Filter
set_option autoImplicit false

theorem mme_stothers_phi233_profile_surplus_of_E_lt_L
    (tau : ℝ) (hEpos : 0 < MME.StothersFourth.E 6 tau)
    (hHpos : 0 < MME.StothersFourth.H 6 tau)
    (hEL : MME.StothersFourth.E 6 tau < MME.StothersFourth.L 6 tau)
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
