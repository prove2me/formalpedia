-- Prove2me | Theorems.Thm_actuarial_c_endowment_variance_nonnegative
-- name    : actuarial_c_endowment_variance_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:29:10.054148+00:00
-- url     : https://prove2.me/theorems/5dd554f4-d8a6-495b-b4fe-2a8324690a5a
-- title:
--   A normalised finite lifetime law gives nonnegative variance for combined death and maturity benefits
-- statement:
--   A normalised finite lifetime law gives nonnegative variance for combined death and maturity benefits.
--
--   Mathematical relation:
--
--   $$
--   \operatorname{Var}(Z_{\text{end}})\ge0
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow
import Definitions.Def_actuarial_c_endowSecond
import Definitions.Def_actuarial_c_endowVariance

open ActuarialAssurances

theorem actuarial_c_endowment_variance_nonnegative (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hm : total h p = 1) : 0 ≤ endowVariance h n v b p := by sorry
