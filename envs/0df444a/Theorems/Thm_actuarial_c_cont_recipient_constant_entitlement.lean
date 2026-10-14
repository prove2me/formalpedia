-- Prove2me | Theorems.Thm_actuarial_c_cont_recipient_constant_entitlement
-- name    : actuarial_c_cont_recipient_constant_entitlement
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:36:39.442979+00:00
-- url     : https://prove2.me/theorems/53eb9635-8fca-457c-8e68-ccc1bf911f8d
-- title:
--   Constant recipient entitlement gives a fixed death amount
-- statement:
--   A constant recipient payment multiplier is algebraically equivalent to an ordinary constant sum assured.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_recipientDeathPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_recipient_constant_entitlement (n delta t c : ℝ) :
    recipientDeathPV n delta t (fun _ => c) =
      c * deathPV n delta t := by sorry
