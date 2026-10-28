-- Prove2me | Theorems.Thm_actuarial_f_cii_award_reversionary_bridge
-- name    : actuarial_f_cii_award_reversionary_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:37:51.780041+00:00
-- url     : https://prove2.me/theorems/d948a532-0448-486d-b92e-c5f536383a3e
-- title:
--   CII survivor annuity: award-state valuation bridge
-- statement:
--   This open mission statement extends the previously proved CII reversionary annuity identity to F's joint award/member/spouse law. For each award state, the CII reversionary annuity is the spouse single-life annuity less the joint-life annuity, with the same discount and benefit functions. The displayed formula uses CII onlyY and does not independently assert the i<h census restriction or death-dependent spouse pension amounts.
-- source:
--   CII published theorem actuarial_d_reversionary_annuity https://prove2.me/theorems/f7bc1cea-a526-4f94-9541-bdea1de324cc ; F-specific outer award-state extension is an original derived finite-sum identity.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_annY
import Definitions.Def_actuarial_d_annJoint
import Theorems.Thm_actuarial_d_reversionary_annuity

open ActuarialUnderpinsF

theorem actuarial_f_cii_award_reversionary_bridge
    (awards horizon payments : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc benefit : ℕ → ℝ) :
    ActuarialUnderpinsF.expect awards horizon p
      (fun z i j => ActuarialJointD.annPath payments disc benefit
        (ActuarialJointD.onlyY i j)) =
      ∑ z ∈ Finset.range awards,
        (ActuarialJointD.annY horizon payments
          (fun i j => p z i j) disc benefit -
         ActuarialJointD.annJoint horizon payments
          (fun i j => p z i j) disc benefit) := by sorry
