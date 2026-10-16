-- Prove2me | Theorems.Thm_actuarial_d_last_prob_inclusion
-- name    : actuarial_d_last_prob_inclusion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:03:18.631284+00:00
-- url     : https://prove2.me/theorems/b5504409-fadd-4859-9ad6-0b38fde67695
-- title:
--   Last-survivor probability identity
-- statement:
--   Last-survivor probability identity. The true joint-survival term corrects double counting, without independence. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{\text{last}}(t)=p_x(t)+p_y(t)-p_{xy}(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.4, p. 147. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_prev
import Definitions.Def_actuarial_d_plast
import Definitions.Def_actuarial_d_pureLast
import Definitions.Def_actuarial_d_pureX
import Definitions.Def_actuarial_d_pureY
import Definitions.Def_actuarial_d_pureJoint

open ActuarialJointD

theorem actuarial_d_last_prob_inclusion (h t : ℕ) (p : ℕ → ℕ → ℝ) : plast h p t = px h p t + py h p t - pxy h p t := by sorry
