-- Prove2me | Theorems.Thm_actuarial_c_delay_composition
-- name    : actuarial_c_delay_composition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:27:56.347238+00:00
-- url     : https://prove2.me/theorems/2cd9320a-f145-45e6-a115-defa088df80a
-- title:
--   Composing two settlement lags accumulates their discount exponents
-- statement:
--   Composing two settlement lags accumulates their discount exponents.
--
--   Mathematical relation:
--
--   $$
--   A^{\text{delay}}(a+b)=v^bA^{\text{delay}}(a)
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.1, claim processing and payment timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_delayPath
import Definitions.Def_actuarial_c_delayEPV

open ActuarialAssurances

theorem actuarial_c_delay_composition (h a b : ℕ) (v : ℝ) (benefit p : ℕ → ℝ) : delayEPV h (a+b) v benefit p=v^b*delayEPV h a v benefit p := by sorry
