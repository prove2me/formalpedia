-- Prove2me | Theorems.Thm_actuarial_c_death_binary
-- name    : actuarial_c_death_binary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:59:05.166272+00:00
-- url     : https://prove2.me/theorems/5eb2bfa4-7b45-4c96-91e9-eca220973bb1
-- title:
--   Each claim event has a binary indicator
-- statement:
--   Each claim event has a binary indicator.
--
--   Mathematical relation:
--
--   $$
--   \mathbf{1}_{\{K=j\}}^2=\mathbf{1}_{\{K=j\}}
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, occurrence and death-year timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death

open ActuarialAssurances

theorem actuarial_c_death_binary (k j : ℕ) : (death k j)^2=death k j := by sorry
