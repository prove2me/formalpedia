-- Prove2me | Theorems.Thm_actuarial_d_guarantee_cashflow_difference
-- name    : actuarial_d_guarantee_cashflow_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:03:07.143978+00:00
-- url     : https://prove2.me/theorems/2ed1aaa9-5e7c-4c30-9b59-16b3c69f1d3b
-- title:
--   Guarantee-overlap cashflow reconciliation
-- statement:
--   Guarantee-overlap cashflow reconciliation. Parallel spouse entitlement produces additional overlapping instalments during the guarantee period. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{\text{parallel}}=Z_{\text{delayed}}+\rho Z_{\text{overlap}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_guaranteeParallelPath
import Definitions.Def_actuarial_d_guaranteeDelayPath
import Definitions.Def_actuarial_d_guaranteeOverlapPath

open ActuarialJointD

theorem actuarial_d_guarantee_cashflow_difference (n g i j : ℕ) (d b : ℕ → ℝ) (rho : ℝ) : guaranteeParallelPath n g d b rho i j = guaranteeDelayPath n g d b rho i j + rho * guaranteeOverlapPath n g d b i j := by sorry
