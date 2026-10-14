-- Prove2me | Theorems.Thm_actuarial_c_zero_assured
-- name    : actuarial_c_zero_assured
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:17:17.632289+00:00
-- url     : https://prove2.me/theorems/a86fee44-ee85-44af-b211-66905cca812e
-- title:
--   Zero insured benefit means zero claim PV
-- statement:
--   Zero insured benefit means zero claim PV.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[Z_0]=0
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, year-end death claim present value, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv

open ActuarialAssurances

theorem actuarial_c_zero_assured (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : epv h v (fun _ => 0) p=0 := by sorry
