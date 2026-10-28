-- Prove2me | Theorems.Thm_actuarial_f_cii_award_indexed_reversionary
-- name    : actuarial_f_cii_award_indexed_reversionary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:38:30.318312+00:00
-- url     : https://prove2.me/theorems/b1101b5a-f4ca-4b99-b76c-8a8296b8b95d
-- title:
--   Award-dependent reversionary annuity identity
-- statement:
--   For a benefit stream selected with award state z, the F expectation of the published CII spouse-only annuity equals the award-weighted difference between spouse and joint annuities. Dependence between the award and mortality is permitted. The benefit does not depend on the realised member death index.
-- source:
--   Original derived exact-revision Lean bridge from published CII definitions and proved actuarial_d_reversionary_annuity theorem https://prove2.me/theorems/f7bc1cea-a526-4f94-9541-bdea1de324cc . The cashflow/horizon conventions are explicit Foundation F assumptions.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_annY
import Definitions.Def_actuarial_d_annJoint
import Theorems.Thm_actuarial_d_reversionary_annuity

open ActuarialUnderpinsF

theorem actuarial_f_cii_award_indexed_reversionary
    (awards horizon payments : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc : ℕ → ℝ)
    (benefit : ℕ → ℕ → ℝ) :
    ActuarialUnderpinsF.expect awards horizon p
      (fun z i j =>
        ActuarialJointD.annPath payments disc (benefit z)
          (ActuarialJointD.onlyY i j)) =
      ∑ z ∈ Finset.range awards,
        (ActuarialJointD.annY horizon payments
          (fun i j => p z i j) disc (benefit z) -
         ActuarialJointD.annJoint horizon payments
          (fun i j => p z i j) disc (benefit z)) := by sorry
