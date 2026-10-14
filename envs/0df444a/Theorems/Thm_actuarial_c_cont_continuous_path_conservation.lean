-- Prove2me | Theorems.Thm_actuarial_c_cont_continuous_path_conservation
-- name    : actuarial_c_cont_continuous_path_conservation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:32:44.495896+00:00
-- url     : https://prove2.me/theorems/417dc93b-3fdf-4161-9ebc-623d73f7e4bc
-- title:
--   Continuous assurance–annuity conservation for each realised lifetime
-- statement:
--   The terminal death-or-maturity payment plus the force-of-interest weighted present value of continuous annuity exposure equals one for each eligible lifetime.
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

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_continuous_path_conservation (n delta t : ℝ)
    (hn : 0 ≤ n) (ht : 0 ≤ t) :
    deathPV n delta t + maturityPV n delta t +
      delta * continuousAnnuityPV n delta t = 1 := by sorry
