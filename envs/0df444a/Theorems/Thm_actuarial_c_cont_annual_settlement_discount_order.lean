-- Prove2me | Theorems.Thm_actuarial_c_cont_annual_settlement_discount_order
-- name    : actuarial_c_cont_annual_settlement_discount_order
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:36:56.930923+00:00
-- url     : https://prove2.me/theorems/e51d7a19-0a10-46ba-9c87-10d48ad630ea
-- title:
--   Immediate death claim is at least as valuable as year-end payment
-- statement:
--   For nonnegative force of interest, settlement at the end of the death year cannot be more valuable than settlement at actual death.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_annualSettlementPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_annual_settlement_discount_order (h : ℕ) (delta t : ℝ)
    (hdelta : 0 ≤ delta) (ht : 0 ≤ t) (horizon : t < (h : ℝ)) :
    annualSettlementPV h delta t ≤ deathPV (h : ℝ) delta t := by sorry
