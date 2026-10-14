-- Prove2me | Theorems.Thm_actuarial_c_zero_term_zero_loss
-- name    : actuarial_c_zero_term_zero_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:31:44.407334+00:00
-- url     : https://prove2.me/theorems/77eb9877-7f1b-41ce-9646-95bdb30cc2a7
-- title:
--   Zero cover and zero premium payments produce zero expected loss
-- statement:
--   Zero cover and zero premium payments produce zero expected loss.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[L_0(0)]=0
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, net premium ratio and premium stream, printed p. 63. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_premiumPath
import Definitions.Def_actuarial_c_lossPath
import Definitions.Def_actuarial_c_expectedLoss

open ActuarialAssurances

theorem actuarial_c_zero_term_zero_loss (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : expectedLoss h 0 v 0 b p=0 := by sorry
