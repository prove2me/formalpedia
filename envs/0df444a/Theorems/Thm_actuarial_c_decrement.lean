-- Prove2me | Theorems.Thm_actuarial_c_decrement
-- name    : actuarial_c_decrement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:14:42.866981+00:00
-- url     : https://prove2.me/theorems/c960905c-3f8a-4e73-ab31-741d4aad8b53
-- title:
--   Death-year mass equals adjacent survival decrement
-- statement:
--   Death-year mass equals adjacent survival decrement.
--
--   Mathematical relation:
--
--   $$
--   S(j)=p_j+S(j+1),\quad j<h
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, occurrence and death-year timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances

theorem actuarial_c_decrement (h j : ℕ) (p : ℕ → ℝ) (hj : j < h) : surv h p j=p j+surv h p (j+1) := by sorry
