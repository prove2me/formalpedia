-- Prove2me | Theorems.Thm_actuarial_c_survival_nonnegative
-- name    : actuarial_c_survival_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:00:16.808078+00:00
-- url     : https://prove2.me/theorems/3fe0715e-d0a5-47da-953c-3b978cf4c997
-- title:
--   Tail survival mass is nonnegative
-- statement:
--   Tail survival mass is nonnegative.
--
--   Mathematical relation:
--
--   $$
--   0\le S(j)
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, occurrence and death-year timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances

theorem actuarial_c_survival_nonnegative (h j : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) : 0 ≤ surv h p j := by sorry
