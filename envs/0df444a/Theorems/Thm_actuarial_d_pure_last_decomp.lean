-- Prove2me | Theorems.Thm_actuarial_d_pure_last_decomp
-- name    : actuarial_d_pure_last_decomp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:03:56.921023+00:00
-- url     : https://prove2.me/theorems/e78e03fb-5898-423a-bfdb-43ac0f3ecb45
-- title:
--   Last-survivor pure endowment identity
-- statement:
--   Last-survivor pure endowment identity. A maturity benefit to either survivor is reconciled using joint survival. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   E_{\text{last}}=E_x+E_y-E_{xy}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.4, p. 147. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_prev
import Definitions.Def_actuarial_d_plast
import Definitions.Def_actuarial_d_pureLast
import Definitions.Def_actuarial_d_pureX
import Definitions.Def_actuarial_d_pureY
import Definitions.Def_actuarial_d_pureJoint

open ActuarialJointD

theorem actuarial_d_pure_last_decomp (h t : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : pureLast h t p d = pureX h t p d + pureY h t p d - pureJoint h t p d := by sorry
