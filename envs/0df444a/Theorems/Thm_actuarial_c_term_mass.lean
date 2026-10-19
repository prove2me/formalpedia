-- Prove2me | Theorems.Thm_actuarial_c_term_mass
-- name    : actuarial_c_term_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:18:05.953143+00:00
-- url     : https://prove2.me/theorems/dbe8ddd0-05d8-4e7e-9706-4b1441b30070
-- title:
--   Temporary death events give the covered discounted death masses
-- statement:
--   Temporary death events give the covered discounted death masses.
--
--   Mathematical relation:
--
--   $$
--   A^{1}_{n|}=\sum_{j=0}^{n-1}v^{j+1}b_jp_j
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

theorem actuarial_c_term_mass (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n ≤ h) : term h n v b p=∑ j ∈ Finset.range n, v^(j+1)*b j*p j := by sorry
