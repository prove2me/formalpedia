-- Prove2me | Theorems.Thm_actuarial_f_cii_spouse_bounded
-- name    : actuarial_f_cii_spouse_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:38:15.805551+00:00
-- url     : https://prove2.me/theorems/fdb95e8e-e46d-4f70-bcda-f26980fce9f4
-- title:
--   Bounded survivor-state equivalence
-- statement:
--   On any instalment date up to the censoring horizon, F's survivor indicator equals the published CII only-spouse-alive indicator. The restriction is essential because F excludes a member recorded as surviving until censoring.
-- source:
--   Original derived exact-revision Lean bridge from published CII definitions and proved actuarial_d_reversionary_annuity theorem https://prove2.me/theorems/f7bc1cea-a526-4f94-9541-bdea1de324cc . The cashflow/horizon conventions are explicit Foundation F assumptions.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_d_onlyY

open ActuarialUnderpinsF

theorem actuarial_f_cii_spouse_bounded (h i j t : ℕ) (ht : t ≤ h) :
    ActuarialUnderpinsF.spouseDue h i j t = ActuarialJointD.onlyY i j t := by sorry
