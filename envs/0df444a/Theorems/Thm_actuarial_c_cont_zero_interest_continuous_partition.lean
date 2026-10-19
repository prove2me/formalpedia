-- Prove2me | Theorems.Thm_actuarial_c_cont_zero_interest_continuous_partition
-- name    : actuarial_c_cont_zero_interest_continuous_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:34:38.133232+00:00
-- url     : https://prove2.me/theorems/beeefdb2-c040-4f7a-a28f-fe130d093c41
-- title:
--   Death or maturity pays one unit at zero interest
-- statement:
--   At zero interest a unit terminal payment is made under exactly one of the death or maturity events.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_maturityPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_zero_interest_continuous_partition (n t : ℝ)
    (hn : 0 ≤ n) (ht : 0 ≤ t) :
    deathPV n 0 t + maturityPV n 0 t = 1 := by sorry
