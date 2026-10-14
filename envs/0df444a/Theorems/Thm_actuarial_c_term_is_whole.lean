-- Prove2me | Theorems.Thm_actuarial_c_term_is_whole
-- name    : actuarial_c_term_is_whole
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:17:52.890984+00:00
-- url     : https://prove2.me/theorems/5689ab3d-875e-4944-86b8-d02d06492eb1
-- title:
--   Cover to final modelled death year is full modelled assurance
-- statement:
--   Cover to final modelled death year is full modelled assurance.
--
--   Mathematical relation:
--
--   $$
--   A^{1}_{h|}=A_h
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.3, term and whole life insurance, printed p. 64. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term

open ActuarialAssurances

theorem actuarial_c_term_is_whole (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : term h h v b p=epv h v b p := by sorry
