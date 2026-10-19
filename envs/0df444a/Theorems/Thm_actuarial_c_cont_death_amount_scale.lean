-- Prove2me | Theorems.Thm_actuarial_c_cont_death_amount_scale
-- name    : actuarial_c_cont_death_amount_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:35:04.104998+00:00
-- url     : https://prove2.me/theorems/eba180df-4e81-47fe-bc4c-7a6f2f802c8c
-- title:
--   Linear scaling by a death sum assured
-- statement:
--   A constant death sum assured scales the realised unit benefit linearly.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_sumAssuredDeathPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_death_amount_scale (n delta amount t : ℝ) :
    sumAssuredDeathPV n delta amount t =
      amount * deathPV n delta t := by sorry
