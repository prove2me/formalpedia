-- Prove2me | Theorems.Thm_actuarial_c_cont_death_variance_nonnegative
-- name    : actuarial_c_cont_death_variance_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:38:31.10599+00:00
-- url     : https://prove2.me/theorems/4a6aad11-f4a9-411c-b91f-dff702e90f06
-- title:
--   Nonnegative death-claim present-value variance
-- statement:
--   For a probability law supported on nonnegative future lifetimes, the second moment dominates the squared expectation.
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
import Definitions.Def_actuarial_c_cont_deathVariance

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_death_variance_nonnegative (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (n delta : ℝ)
    (hn : 0 ≤ n) (hsupport : μ {t : ℝ | 0 ≤ t} = 1) :
    0 ≤ deathVariance μ n delta := by sorry
