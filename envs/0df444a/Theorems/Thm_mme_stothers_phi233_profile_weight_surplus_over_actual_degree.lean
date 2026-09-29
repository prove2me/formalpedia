-- Prove2me | Theorems.Thm_mme_stothers_phi233_profile_weight_surplus_over_actual_degree
-- name    : mme_stothers_phi233_profile_weight_surplus_over_actual_degree
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-07T02:35:09.326712+00:00
-- url     : https://prove2.me/theorems/e11f3b14-0d01-4ebb-b644-a81ea5eb2392
-- title:
--   A finite phi_233 profile surpasses the explicit ambient-degree hash loss
-- statement:
--   Fix $\tau$ with $2\le3\tau\le3$ and a nonnegative base $V$ strictly below the cubed $\varphi_{233}$ rate in Lemma 5.1(v). There is a positive integer profile length $N$, nonnegative counts $(\alpha,\beta,\gamma,\delta)$ with $2\alpha+\beta+\gamma+\delta=N$, and an exact profile address such that
--
--   $$
--   V^{2N}D\exp\bigl(4000\sqrt{18N+1}\bigr)<T B.
--   $$
--
--   Here $D$ is the product of the three ambient same-marginal fiber cardinalities through that address; $T$ is the number of exact cyclic profile edges; and $B$ is the product of the ten component cyclic rates raised to their exact profile multiplicities. In the source ordering, those rates are
--
--   $$
--   (EH,HL,EH,E^2,L^2,L^2,E^2,EH,HL,EH),
--   $$
--
--   and their multiplicities are
--
--   $$
--   (\alpha,\beta,\alpha,\gamma,\delta,\delta,\gamma,\alpha,\beta,\alpha).
--   $$
--
--   This is the finite, strict-surplus form of the stationary-profile limit in Lemma 5.1(v). It keeps the actual same-marginal degree and the explicit subexponential hash loss. The statement is purely combinatorial and analytic; it assumes no tensor restriction or constituent value conclusion.
-- source:
--   Davie and Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3, Equation (3.6), and Lemma 5.1(v), printed pp. 356–360 and 366; https://webhomes.maths.ed.ac.uk/~sandy/a11164.pdf. Finite strict-surplus form with the explicit prime–Behrend loss from mme_prime_behrend_dominates_bounded_collision_degree.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi233_cyclic_finsets

open MME BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false

theorem mme_stothers_phi233_profile_weight_surplus_over_actual_degree
    (tau : ℝ) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
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
