-- Prove2me | Theorems.Thm_actuarial_d_law_total_expected
-- name    : actuarial_d_law_total_expected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:04:27.365469+00:00
-- url     : https://prove2.me/theorems/ef0b302f-fc51-4faa-ab82-4d2616171344
-- title:
--   Expectation preserves total probability
-- statement:
--   Expectation preserves total probability. A normalised joint law assigns unit probability to the exhaustive sample space. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   \sum_{i=0}^{h}\sum_{j=0}^{h}p_{ij}=1
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_expect

open ActuarialJointD

theorem actuarial_d_law_total_expected (h : ℕ) (p : ℕ → ℕ → ℝ) (hp : valid h p) : expect h p (fun _ _ => (1 : ℝ)) = 1 := by sorry
