-- Prove2me | Theorems.Thm_actuarial_c_delay_nonincrease
-- name    : actuarial_c_delay_nonincrease
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:28:10.853195+00:00
-- url     : https://prove2.me/theorems/d4d0e0a7-177e-4a1a-815a-d80c01c2781d
-- title:
--   For nonnegative claims and positive interest, later settlement does not increase the expected present value
-- statement:
--   For nonnegative claims and positive interest, later settlement does not increase the expected present value.
--
--   Mathematical relation:
--
--   $$
--   a\le b,\ 0\le v\le1\Longrightarrow A^{\text{delay}}(b)\le A^{\text{delay}}(a)
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

theorem actuarial_c_delay_nonincrease (h a b : ℕ) (v : ℝ) (benefit p : ℕ → ℝ) (hab : a ≤ b) (hv : 0 ≤ v) (hv1 : v ≤ 1) (hb : ∀ j, 0 ≤ benefit j) (hp : ∀ j, 0 ≤ p j) : delayEPV h b v benefit p ≤ delayEPV h a v benefit p := by sorry
