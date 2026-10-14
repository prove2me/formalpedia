-- Prove2me | Theorems.Thm_actuarial_c_alive_zero
-- name    : actuarial_c_alive_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:59:16.832599+00:00
-- url     : https://prove2.me/theorems/fa546f7f-b3f4-40e8-be6d-8ca8841acbf6
-- title:
--   Life is in force at valuation
-- statement:
--   Life is in force at valuation.
--
--   Mathematical relation:
--
--   $$
--   \mathbf{1}_{\{K\ge0\}}=1
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, occurrence and death-year timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive

open ActuarialAssurances

theorem actuarial_c_alive_zero (k : ℕ) : alive k 0=1 := by sorry
