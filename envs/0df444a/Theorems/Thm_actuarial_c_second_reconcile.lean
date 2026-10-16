-- Prove2me | Theorems.Thm_actuarial_c_second_reconcile
-- name    : actuarial_c_second_reconcile
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:23:52.112976+00:00
-- url     : https://prove2.me/theorems/a49543ac-ea9d-477b-8827-5fa4c1fe139a
-- title:
--   Mutually exclusive claims eliminate cross-terms in squared PV
-- statement:
--   Mutually exclusive claims eliminate cross-terms in squared PV.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[Z^2]=\sum_{j=0}^{h-1}v^{2(j+1)}b_j^2p_j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_second
import Definitions.Def_actuarial_c_secondMass

open ActuarialAssurances

theorem actuarial_c_second_reconcile (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : second h v b p=secondMass h v b p := by sorry
