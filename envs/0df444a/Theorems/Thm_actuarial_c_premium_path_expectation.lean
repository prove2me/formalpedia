-- Prove2me | Theorems.Thm_actuarial_c_premium_path_expectation
-- name    : actuarial_c_premium_path_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:30:19.607801+00:00
-- url     : https://prove2.me/theorems/79490d09-f84a-402e-a962-ac062d14483c
-- title:
--   The actual discounted premium instalments reconcile with annuity-due survival weighting
-- statement:
--   The actual discounted premium instalments reconcile with annuity-due survival weighting.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Y_n]=\ddot a_n
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, net premium ratio and premium stream, printed p. 63. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_due
import Definitions.Def_actuarial_c_premiumPath

open ActuarialAssurances

theorem actuarial_c_premium_path_expectation (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) : (∑ k ∈ Finset.range (h+1), p k*premiumPath n v k)=due h n v p := by sorry
