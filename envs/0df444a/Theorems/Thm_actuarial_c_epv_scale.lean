-- Prove2me | Theorems.Thm_actuarial_c_epv_scale
-- name    : actuarial_c_epv_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:16:47.275018+00:00
-- url     : https://prove2.me/theorems/1ce5a24e-8920-48e1-aadc-b25c6fdb0065
-- title:
--   Expected claims inherit scale
-- statement:
--   Expected claims inherit scale.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[Z_{cb}]=c\mathbb{E}[Z_b]
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

theorem actuarial_c_epv_scale (h : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : epv h v (fun j => c*b j) p=c*epv h v b p := by sorry
