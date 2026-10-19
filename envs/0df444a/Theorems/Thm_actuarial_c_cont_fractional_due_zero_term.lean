-- Prove2me | Theorems.Thm_actuarial_c_cont_fractional_due_zero_term
-- name    : actuarial_c_cont_fractional_due_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:36:17.88445+00:00
-- url     : https://prove2.me/theorems/e998b491-3315-49f9-af9a-cc0ede621755
-- title:
--   Zero-duration m-thly annuity has zero value
-- statement:
--   A due annuity with no insured years has no scheduled payments irrespective of death time.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_cont_fractionalDuePV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_fractional_due_zero_term (m : ℕ) (delta t : ℝ) :
    fractionalDuePV m 0 delta t = 0 := by sorry
