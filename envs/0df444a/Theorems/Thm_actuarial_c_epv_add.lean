-- Prove2me | Theorems.Thm_actuarial_c_epv_add
-- name    : actuarial_c_epv_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:17:05.814135+00:00
-- url     : https://prove2.me/theorems/fce8be63-3ba9-45a9-8b68-6abce13ae5fb
-- title:
--   Expected combined benefits add
-- statement:
--   Expected combined benefits add.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[Z_{b+c}]=\mathbb{E}[Z_b]+\mathbb{E}[Z_c]
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

theorem actuarial_c_epv_add (h : ℕ) (v : ℝ) (b c p : ℕ → ℝ) : epv h v (fun j => b j+c j) p=epv h v b p+epv h v c p := by sorry
