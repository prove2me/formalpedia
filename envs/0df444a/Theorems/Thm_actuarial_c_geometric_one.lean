-- Prove2me | Theorems.Thm_actuarial_c_geometric_one
-- name    : actuarial_c_geometric_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:22:19.008985+00:00
-- url     : https://prove2.me/theorems/9e71720e-5d08-4aa9-9818-b8ca252ac5cd
-- title:
--   No geometric escalation preserves initial cover
-- statement:
--   No geometric escalation preserves initial cover.
--
--   Mathematical relation:
--
--   $$
--   1^j=1
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, variable death-benefit vector, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_geom

open ActuarialAssurances

theorem actuarial_c_geometric_one (j : ℕ) : geom 1 j=1 := by sorry
