-- Prove2me | Theorems.Thm_actuarial_c_cont_zero_interest_continuous_annuity
-- name    : actuarial_c_cont_zero_interest_continuous_annuity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:34:09.821674+00:00
-- url     : https://prove2.me/theorems/6b86740b-2f97-4402-9a19-cc1ff055fc2a
-- title:
--   Continuous annuity at zero interest equals exposed duration
-- statement:
--   At zero force of interest the continuously paid annuity present value reduces exactly to exposure duration.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_exposure
import Definitions.Def_actuarial_c_cont_continuousAnnuityPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_zero_interest_continuous_annuity (n t : ℝ) :
    continuousAnnuityPV n 0 t = exposure n t := by sorry
