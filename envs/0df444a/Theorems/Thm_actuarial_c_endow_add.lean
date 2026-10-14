-- Prove2me | Theorems.Thm_actuarial_c_endow_add
-- name    : actuarial_c_endow_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:20:38.940622+00:00
-- url     : https://prove2.me/theorems/c681203a-5b43-4950-91eb-187f5ffd65dc
-- title:
--   Endowment decomposes into disjoint death and survival payouts
-- statement:
--   Endowment decomposes into disjoint death and survival payouts.
--
--   Mathematical relation:
--
--   $$
--   A^{\text{end}}_{n|}=A^{1}_{n|}+{}_nE
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_pure
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow

open ActuarialAssurances

theorem actuarial_c_endow_add (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) : endow h n v b p=term h n v b p+pure h n v p := by sorry
