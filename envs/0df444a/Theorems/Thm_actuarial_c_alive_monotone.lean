-- Prove2me | Theorems.Thm_actuarial_c_alive_monotone
-- name    : actuarial_c_alive_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:59:29.969222+00:00
-- url     : https://prove2.me/theorems/5e665d0e-7d52-4fbb-a921-328fec2d47b9
-- title:
--   Later survival implies earlier survival
-- statement:
--   Later survival implies earlier survival.
--
--   Mathematical relation:
--
--   $$
--   \mathbf{1}_{\{K\ge j\}}\le\mathbf{1}_{\{K\ge i\}},\quad i\le j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, occurrence and death-year timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive

open ActuarialAssurances

theorem actuarial_c_alive_monotone (k i j : ℕ) (hij : i ≤ j) : alive k j ≤ alive k i := by sorry
