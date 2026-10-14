-- Prove2me | Theorems.Thm_actuarial_c_endow_now
-- name    : actuarial_c_endow_now
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:21:29.041193+00:00
-- url     : https://prove2.me/theorems/c723c6a2-0c2b-46a5-9421-ab13260c7f86
-- title:
--   Zero-term endowment pays at inception
-- statement:
--   Zero-term endowment pays at inception.
--
--   Mathematical relation:
--
--   $$
--   A^{\text{end}}_{0|}=1
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow

open ActuarialAssurances

theorem actuarial_c_endow_now (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : endow h 0 v b p=total h p := by sorry
