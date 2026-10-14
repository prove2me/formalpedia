-- Prove2me | Theorems.Thm_actuarial_c_net_premium_zero_expected_loss
-- name    : actuarial_c_net_premium_zero_expected_loss
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:31:23.834981+00:00
-- url     : https://prove2.me/theorems/c1d0a58c-fdae-49ab-9d3a-cc1517606d5e
-- title:
--   Expected net loss vanishes at the equivalence premium under a valid annuity denominator
-- statement:
--   Expected net loss vanishes at the equivalence premium under a valid annuity denominator.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[L(P_{\text{net}})]=0
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, net premium ratio and premium stream, printed p. 63. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_due
import Definitions.Def_actuarial_c_premiumPath
import Definitions.Def_actuarial_c_lossPath
import Definitions.Def_actuarial_c_expectedLoss
import Definitions.Def_actuarial_c_netPremium

open ActuarialAssurances

theorem actuarial_c_net_premium_zero_expected_loss (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (ha : 0 < due h n v p) : expectedLoss h n v (netPremium h n v b p) b p=0 := by sorry
