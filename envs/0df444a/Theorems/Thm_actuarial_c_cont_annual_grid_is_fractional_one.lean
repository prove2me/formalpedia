-- Prove2me | Theorems.Thm_actuarial_c_cont_annual_grid_is_fractional_one
-- name    : actuarial_c_cont_annual_grid_is_fractional_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:37:35.368269+00:00
-- url     : https://prove2.me/theorems/a225a9cb-e823-40e6-937d-842d00273e4f
-- title:
--   Annual death settlement equals the unit-frequency fractional model
-- statement:
--   One payment subperiod per policy year reproduces exactly the ordinary year-end death-claim settlement value.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_cont_annualSettlementPV
import Definitions.Def_actuarial_c_cont_fractionalSettlementPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_annual_grid_is_fractional_one (h : ℕ) (delta t : ℝ) :
    fractionalSettlementPV 1 h delta t = annualSettlementPV h delta t := by sorry
