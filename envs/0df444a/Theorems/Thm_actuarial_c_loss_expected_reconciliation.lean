-- Prove2me | Theorems.Thm_actuarial_c_loss_expected_reconciliation
-- name    : actuarial_c_loss_expected_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:30:38.801981+00:00
-- url     : https://prove2.me/theorems/8d06b905-4aa6-401a-a125-af8e5731e1a1
-- title:
--   The net insurer loss random variable has expected value claims less expected premiums
-- statement:
--   The net insurer loss random variable has expected value claims less expected premiums.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[L]=A_n-P\ddot a_n
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

open ActuarialAssurances

theorem actuarial_c_loss_expected_reconciliation (h n : ℕ) (v premium : ℝ) (b p : ℕ → ℝ) : expectedLoss h n v premium b p=term h n v b p-premium*due h n v p := by sorry
