-- Prove2me | Theorems.Thm_actuarial_c_pure_now
-- name    : actuarial_c_pure_now
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:20:23.282984+00:00
-- url     : https://prove2.me/theorems/285c446c-7856-44b1-91ed-e3a071d7871f
-- title:
--   Immediate maturity lump sum equals whole mass
-- statement:
--   Immediate maturity lump sum equals whole mass.
--
--   Mathematical relation:
--
--   $$
--   {}_0E=\sum_{j=0}^{h}p_j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_pure

open ActuarialAssurances

theorem actuarial_c_pure_now (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : pure h 0 v p=total h p := by sorry
