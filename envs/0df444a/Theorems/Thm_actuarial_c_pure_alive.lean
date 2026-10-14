-- Prove2me | Theorems.Thm_actuarial_c_pure_alive
-- name    : actuarial_c_pure_alive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:19:45.585059+00:00
-- url     : https://prove2.me/theorems/a79a26d5-e4f6-480f-8287-5642e74fbbfb
-- title:
--   Maturity survivor receives the entire lump sum
-- statement:
--   Maturity survivor receives the entire lump sum.
--
--   Mathematical relation:
--
--   $$
--   v^n\mathbf{1}_{\{K\ge n\}}=v^n,\quad K\ge n
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

theorem actuarial_c_pure_alive (n k : ℕ) (v : ℝ) (hk : n ≤ k) : purePath n k v=v^n := by sorry
