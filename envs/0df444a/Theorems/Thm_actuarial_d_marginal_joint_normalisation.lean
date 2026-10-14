-- Prove2me | Theorems.Thm_actuarial_d_marginal_joint_normalisation
-- name    : actuarial_d_marginal_joint_normalisation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T07:04:13.157977+00:00
-- url     : https://prove2.me/theorems/1d7e4552-8727-44c4-9705-9c934dce8070
-- title:
--   Normalised survival at commencement
-- statement:
--   Normalised survival at commencement. The single and joint survival probabilities are all one at the issue date of this model. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_x(0)=p_y(0)=p_{xy}(0)=1
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_expect

open ActuarialJointD

theorem actuarial_d_marginal_joint_normalisation (h : ℕ) (p : ℕ → ℕ → ℝ) (hp : valid h p) : px h p 0 = 1 ∧ py h p 0 = 1 ∧ pxy h p 0 = 1 := by sorry
