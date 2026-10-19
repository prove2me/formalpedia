-- Prove2me | Theorems.Thm_actuarial_c_cont_time_lag_factor
-- name    : actuarial_c_cont_time_lag_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:34:49.36155+00:00
-- url     : https://prove2.me/theorems/c8295c6e-6f88-45eb-b00e-3a75fbedb2e8
-- title:
--   Immediate death benefit with an added settlement lag
-- statement:
--   A fixed lag after actual death multiplies the death-payment present value by its exponential discount factor.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_laggedDeathPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_time_lag_factor (n delta lag t : ℝ) :
    laggedDeathPV n delta lag t =
      Real.exp (-delta * lag) * deathPV n delta t := by sorry
