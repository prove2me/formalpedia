-- Prove2me | Theorems.Thm_actuarial_c_cont_immediate_death_second_moment
-- name    : actuarial_c_cont_immediate_death_second_moment
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:38:11.760231+00:00
-- url     : https://prove2.me/theorems/5acd018c-ee25-4bcb-8dc8-b2604f9d0e5c
-- title:
--   Immediate death-claim second moment uses doubled force of interest
-- statement:
--   For an exclusive one-off death claim, the second moment is the same immediate-death expectation evaluated at twice the force of interest.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_deathEPV
import Definitions.Def_actuarial_c_cont_deathSecondEPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_immediate_death_second_moment (μ : Measure ℝ) (n delta : ℝ) :
    deathSecondEPV μ n delta =
      deathEPV μ n (2*delta) := by sorry
