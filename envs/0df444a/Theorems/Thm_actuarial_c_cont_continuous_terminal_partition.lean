-- Prove2me | Theorems.Thm_actuarial_c_cont_continuous_terminal_partition
-- name    : actuarial_c_cont_continuous_terminal_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:32:26.736929+00:00
-- url     : https://prove2.me/theorems/742f3c0f-d179-4068-a194-4af1aed9f595
-- title:
--   Disjoint death and maturity payments give the terminal discounted cashflow
-- statement:
--   Death before maturity and survival to maturity partition every nonnegative lifetime, including exact death at maturity, and their terminal cashflow PV equals discounting to the earlier time.
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

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_continuous_terminal_partition (n delta t : ℝ)
    (hn : 0 ≤ n) (ht : 0 ≤ t) :
    deathPV n delta t + maturityPV n delta t =
      Real.exp (-delta * exposure n t) := by sorry
