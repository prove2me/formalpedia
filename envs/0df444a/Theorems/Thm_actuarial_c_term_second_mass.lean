-- Prove2me | Theorems.Thm_actuarial_c_term_second_mass
-- name    : actuarial_c_term_second_mass
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:28:41.816333+00:00
-- url     : https://prove2.me/theorems/a824aa3b-20b1-4b80-b13d-07f7f5b17d2d
-- title:
--   The term-assurance second moment is the disjoint covered death masses weighted by squared benefits
-- statement:
--   The term-assurance second moment is the disjoint covered death masses weighted by squared benefits.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z_n^2]=\sum_{j=0}^{n-1}v^{2(j+1)}b_j^2p_j
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_termSecond

open ActuarialAssurances

theorem actuarial_c_term_second_mass (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n ≤ h) : termSecond h n v b p=∑ j ∈ Finset.range n, v^(2*(j+1))*(b j)^2*p j := by sorry
