-- Prove2me | Theorems.Thm_actuarial_c_cont_continuous_distribution_conservation
-- name    : actuarial_c_cont_continuous_distribution_conservation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:33:09.52898+00:00
-- url     : https://prove2.me/theorems/574964c9-c812-486b-967f-e0abb7224b2b
-- title:
--   Continuous assurance–annuity conservation under a probability law
-- statement:
--   For a probability law supported on nonnegative future lifetimes, averaging the pathwise identity recovers the continuous insurance–annuity identity without assuming a density.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_exposure
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_maturityPV
import Definitions.Def_actuarial_c_cont_continuousAnnuityPV
import Definitions.Def_actuarial_c_cont_deathEPV
import Definitions.Def_actuarial_c_cont_maturityEPV
import Definitions.Def_actuarial_c_cont_continuousAnnuityEPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_continuous_distribution_conservation (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (n delta : ℝ) (hn : 0 ≤ n)
    (hsupport : μ {t : ℝ | 0 ≤ t} = 1) :
    deathEPV μ n delta + maturityEPV μ n delta +
      delta * continuousAnnuityEPV μ n delta = 1 := by sorry
