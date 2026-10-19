-- Prove2me | Theorems.Thm_actuarial_c_cont_death_maturity_exclusive
-- name    : actuarial_c_cont_death_maturity_exclusive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:33:34.346982+00:00
-- url     : https://prove2.me/theorems/a3e67630-d5be-4257-874c-02b9a2070f2c
-- title:
--   Death benefit and maturity benefit are mutually exclusive
-- statement:
--   The death and maturity payoff indicators never overlap, including positive atoms at the maturity boundary.
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

theorem actuarial_c_cont_death_maturity_exclusive (n delta t : ℝ) :
    deathPV n delta t * maturityPV n delta t = 0 := by sorry
