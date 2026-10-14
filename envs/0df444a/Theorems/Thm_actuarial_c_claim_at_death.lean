-- Prove2me | Theorems.Thm_actuarial_c_claim_at_death
-- name    : actuarial_c_claim_at_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:15:37.692415+00:00
-- url     : https://prove2.me/theorems/a0eeffdd-ffd2-4891-a4cb-9993bcd30e81
-- title:
--   One death leads to one claim at the following year-end
-- statement:
--   One death leads to one claim at the following year-end.
--
--   Mathematical relation:
--
--   $$
--   Z(k)=v^{k+1}b_k,\quad k<h
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, year-end death claim present value, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path

open ActuarialAssurances

theorem actuarial_c_claim_at_death (h k : ℕ) (v : ℝ) (b : ℕ → ℝ) (hk : k < h) : path h v b k=v^(k+1)*b k := by sorry
