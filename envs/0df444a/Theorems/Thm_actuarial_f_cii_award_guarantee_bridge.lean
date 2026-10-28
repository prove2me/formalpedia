-- Prove2me | Theorems.Thm_actuarial_f_cii_award_guarantee_bridge
-- name    : actuarial_f_cii_award_guarantee_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:38:04.704407+00:00
-- url     : https://prove2.me/theorems/63c59c2a-79a6-4ae6-907d-91a72323cd92
-- title:
--   CII guarantee: award-state overlap bridge
-- statement:
--   This open mission statement extends the published CII comparison of parallel survivor instalments and guarantee-then-reversion to F's extra award state. It assumes CII's same benefit and discount functions in each two-life cell. It is a mathematical cashflow identity for the CII guarantee model and does not discharge statutory survivor GMP or handle F's death-dependent award.
-- source:
--   CII published theorem actuarial_d_guarantee_value_difference https://prove2.me/theorems/7b4f9a4a-11e8-40d1-bed9-1f0f016dbc0c ; F-specific outer award-state extension is an original derived finite-sum identity.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_d_guaranteeParallelPath
import Definitions.Def_actuarial_d_guaranteeParallelValue
import Definitions.Def_actuarial_d_guaranteeDelayValue
import Definitions.Def_actuarial_d_guaranteeOverlapValue
import Theorems.Thm_actuarial_d_guarantee_value_difference

open ActuarialUnderpinsF

theorem actuarial_f_cii_award_guarantee_bridge
    (awards horizon payments guaranteed : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc benefit : ℕ → ℝ) (rho : ℝ) :
    ActuarialUnderpinsF.expect awards horizon p
      (fun z i j =>
        ActuarialJointD.guaranteeParallelPath payments guaranteed
          disc benefit rho i j) =
      ∑ z ∈ Finset.range awards,
        (ActuarialJointD.guaranteeDelayValue horizon payments guaranteed
          (fun i j => p z i j) disc benefit rho +
         rho * ActuarialJointD.guaranteeOverlapValue horizon payments guaranteed
          (fun i j => p z i j) disc benefit) := by sorry
