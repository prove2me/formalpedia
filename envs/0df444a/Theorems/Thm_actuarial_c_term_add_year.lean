-- Prove2me | Theorems.Thm_actuarial_c_term_add_year
-- name    : actuarial_c_term_add_year
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:18:23.695147+00:00
-- url     : https://prove2.me/theorems/db3954ee-53a4-4c50-8606-5d621453c41f
-- title:
--   Next year of coverage adds one new death event
-- statement:
--   Next year of coverage adds one new death event.
--
--   Mathematical relation:
--
--   $$
--   A^{1}_{n+1|}=A^{1}_{n|}+v^{n+1}b_np_n
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.3, term and whole life insurance, printed p. 64. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term

open ActuarialAssurances

theorem actuarial_c_term_add_year (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n < h) : term h (n+1) v b p=term h n v b p+v^(n+1)*b n*p n := by sorry
