-- Prove2me | Theorems.Thm_actuarial_d_reversion_prob
-- name    : actuarial_d_reversion_prob
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:03:34.68828+00:00
-- url     : https://prove2.me/theorems/09697a0b-1bbe-4059-b7e4-b8d97e98d275
-- title:
--   Spouse reversion probability
-- statement:
--   Spouse reversion probability. Reversionary eligibility is spouse survival less joint survival. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{y\mid x}(t)=p_y(t)-p_{xy}(t)
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

theorem actuarial_d_reversion_prob (h t : ℕ) (p : ℕ → ℕ → ℝ) : prev h p t = py h p t - pxy h p t := by sorry
