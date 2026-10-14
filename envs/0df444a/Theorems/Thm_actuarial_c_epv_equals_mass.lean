-- Prove2me | Theorems.Thm_actuarial_c_epv_equals_mass
-- name    : actuarial_c_epv_equals_mass
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:16:32.027353+00:00
-- url     : https://prove2.me/theorems/0eda5096-ed34-4373-b297-7b367aab4a02
-- title:
--   Average actual claims and death-mass projection agree
-- statement:
--   Average actual claims and death-mass projection agree.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[Z]=\sum_{j=0}^{h-1}v^{j+1}b_jp_j
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
import Definitions.Def_actuarial_c_massPV

open ActuarialAssurances

theorem actuarial_c_epv_equals_mass (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : epv h v b p=massPV h v b p := by sorry
