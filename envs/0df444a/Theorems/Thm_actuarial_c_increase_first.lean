-- Prove2me | Theorems.Thm_actuarial_c_increase_first
-- name    : actuarial_c_increase_first
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:21:38.944171+00:00
-- url     : https://prove2.me/theorems/ada638e2-8cef-48fd-a50c-ac7b12a79ed3
-- title:
--   Increasing insurance begins at one unit
-- statement:
--   Increasing insurance begins at one unit.
--
--   Mathematical relation:
--
--   $$
--   b^{\uparrow}_0=1
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, variable death-benefit vector, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_inc

open ActuarialAssurances

theorem actuarial_c_increase_first  : inc 0=1 := by sorry
