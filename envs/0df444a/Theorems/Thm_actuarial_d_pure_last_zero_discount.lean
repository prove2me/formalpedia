-- Prove2me | Theorems.Thm_actuarial_d_pure_last_zero_discount
-- name    : actuarial_d_pure_last_zero_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:04:40.992022+00:00
-- url     : https://prove2.me/theorems/274ebd8e-34c4-4982-bd72-1d16b66fc8e8
-- title:
--   Pure endowment zero-discount limit
-- statement:
--   Pure endowment zero-discount limit. A zero payment-date discount function produces no current endowment value. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   E_{\text{last}}(t;d_t=0)=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.4, p. 147. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_pureLast
import Definitions.Def_actuarial_d_plast

open ActuarialJointD

theorem actuarial_d_pure_last_zero_discount (h t : ℕ) (p : ℕ → ℕ → ℝ) : pureLast h t p (fun _ => 0) = 0 := by sorry
