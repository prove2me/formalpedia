-- Prove2me | Theorems.Thm_actuarial_c_net_premium_balance
-- name    : actuarial_c_net_premium_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:31:03.934985+00:00
-- url     : https://prove2.me/theorems/a2ca0a9c-0515-4b90-8a4a-577e56ea4b42
-- title:
--   Net premium achieves actuarial equivalence only for a strictly positive premium-annuity denominator
-- statement:
--   Net premium achieves actuarial equivalence only for a strictly positive premium-annuity denominator.
--
--   Mathematical relation:
--
--   $$
--   P_{\text{net}}\ddot a_n=A_n,\quad\ddot a_n>0
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
import Definitions.Def_actuarial_c_netPremium

open ActuarialAssurances

theorem actuarial_c_net_premium_balance (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (ha : 0 < due h n v p) : netPremium h n v b p*due h n v p=term h n v b p := by sorry
