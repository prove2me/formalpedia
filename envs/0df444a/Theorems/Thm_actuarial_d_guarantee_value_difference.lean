-- Prove2me | Theorems.Thm_actuarial_d_guarantee_value_difference
-- name    : actuarial_d_guarantee_value_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:03:23.512445+00:00
-- url     : https://prove2.me/theorems/7b4f9a4a-11e8-40d1-bed9-1f0f016dbc0c
-- title:
--   Guarantee overlap as an additional liability
-- statement:
--   Guarantee overlap as an additional liability. Expectation preserves the specific extra spouse payment cashflow during an in-force member guarantee. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{parallel}}=V_{\text{delayed}}+\rho V_{\text{overlap}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_guaranteeParallelValue
import Definitions.Def_actuarial_d_guaranteeDelayValue
import Definitions.Def_actuarial_d_guaranteeOverlapValue

open ActuarialJointD

theorem actuarial_d_guarantee_value_difference (h n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : guaranteeParallelValue h n g p d b rho = guaranteeDelayValue h n g p d b rho + rho * guaranteeOverlapValue h n g p d b := by sorry
