-- Prove2me | Theorems.Thm_actuarial_c_pure_dead
-- name    : actuarial_c_pure_dead
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:19:33.180258+00:00
-- url     : https://prove2.me/theorems/c16e610d-9203-4b65-bad8-97ac608a5f2f
-- title:
--   Death before maturity means no survival benefit
-- statement:
--   Death before maturity means no survival benefit.
--
--   Mathematical relation:
--
--   $$
--   v^n\mathbf{1}_{\{K\ge n\}}=0,\quad K<n
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_purePath

open ActuarialAssurances

theorem actuarial_c_pure_dead (n k : ℕ) (v : ℝ) (hk : k < n) : purePath n k v=0 := by sorry
