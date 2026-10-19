-- Prove2me | Theorems.Thm_actuarial_c_cont_fractional_grid_start
-- name    : actuarial_c_cont_fractional_grid_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:35:37.774096+00:00
-- url     : https://prove2.me/theorems/b7ce5e46-39a6-48f8-a708-487f7f194c0c
-- title:
--   Fractional payment grid begins at time zero
-- statement:
--   The first m-thly policy instant is time zero when the positive payment frequency is defined.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_fractionalTime

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_fractional_grid_start (m : ℕ) (hm : 0 < m) :
    fractionalTime m 0 = 0 := by sorry
