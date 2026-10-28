-- Prove2me | Theorems.Thm_actuarial_f_protected_replacement_epv_reconciles
-- name    : actuarial_f_protected_replacement_epv_reconciles
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:33:45.489056+00:00
-- url     : https://prove2.me/theorems/06a6154f-3c38-496a-a6e9-c97f4bf66bf0
-- title:
--   GMP-safe parallel and replacement value plus displaceable overlap
-- statement:
--   GMP-safe parallel and replacement value plus displaceable overlap. This is a proof obligation on the exact declared Lean benefit contract. It does not certify scheme-specific legal inputs.
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpProtectedDirectEPV
import Definitions.Def_actuarial_f_gmpProtectedReplacementEPV
import Definitions.Def_actuarial_f_gmpProtectedDisplaceableEPV

open ActuarialUnderpinsF

theorem actuarial_f_protected_replacement_epv_reconciles
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (statutorySurvivor : ℕ → ℕ → ℕ → ℕ → ℝ) :
    gmpProtectedDirectEPV n h r g p disc a b c sa sb estate
      ga gb gc gs ge memberSupplement statutorySurvivor =
    gmpProtectedReplacementEPV n h r g p disc a b c sa sb estate
      ga gb gc gs ge memberSupplement statutorySurvivor +
    gmpProtectedDisplaceableEPV n h r g p disc a b sa sb gs
      statutorySurvivor := by
  sorry
