-- Prove2me | Theorems.Thm_actuarial_d_advanced_specialises_without_guarantee
-- name    : actuarial_d_advanced_specialises_without_guarantee
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:31:30.757329+00:00
-- url     : https://prove2.me/theorems/efd4e4b3-4709-4c60-b396-d8928a79ea29
-- title:
--   Advanced contract recovers the ordinary spouse continuation
-- statement:
--   Advanced contract recovers the ordinary spouse continuation. Zero guarantee and zero deferral exactly recover the original member-and-spouse cashflow, including the same death claim timing. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{a=0,g=0}=V_{\text{ordinary member+spouse}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_advancedValue
import Definitions.Def_actuarial_d_totalValue

open ActuarialJointD

theorem actuarial_d_advanced_specialises_without_guarantee (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) : advancedValue h 0 n 0 p d b rho f s fx fy ft = totalValue h n p d b rho f s fx fy ft := by sorry
