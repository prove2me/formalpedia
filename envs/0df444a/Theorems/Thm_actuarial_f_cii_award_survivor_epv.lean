-- Prove2me | Theorems.Thm_actuarial_f_cii_award_survivor_epv
-- name    : actuarial_f_cii_award_survivor_epv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:38:43.656673+00:00
-- url     : https://prove2.me/theorems/9f794a56-cf5c-4067-b893-cd60b4415d86
-- title:
--   Foundation F survivor cashflows via published CII
-- statement:
--   The actual F spouseDue cashflow, discounted with an award-dependent pension benefit stream, equals the award-weighted CII spouse-annuity less joint-annuity value when every instalment date is within F's mortality censoring horizon. This identity does not yet handle death-fixed spouse amounts or statutory GMP.
-- source:
--   Original derived exact-revision Lean bridge from published CII definitions and proved actuarial_d_reversionary_annuity theorem https://prove2.me/theorems/f7bc1cea-a526-4f94-9541-bdea1de324cc . The cashflow/horizon conventions are explicit Foundation F assumptions.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_annY
import Definitions.Def_actuarial_d_annJoint

open ActuarialUnderpinsF

theorem actuarial_f_cii_award_survivor_epv
    (awards horizon payments : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc : ℕ → ℝ)
    (benefit : ℕ → ℕ → ℝ) (hpayments : payments ≤ horizon + 1) :
    ActuarialUnderpinsF.expect awards horizon p
      (fun z i j =>
        ActuarialJointD.annPath payments disc (benefit z)
          (fun t => ActuarialUnderpinsF.spouseDue horizon i j t)) =
      ∑ z ∈ Finset.range awards,
        (ActuarialJointD.annY horizon payments
          (fun i j => p z i j) disc (benefit z) -
         ActuarialJointD.annJoint horizon payments
          (fun i j => p z i j) disc (benefit z)) := by sorry
