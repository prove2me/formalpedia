-- Prove2me | Theorems.Thm_actuarial_f_gmp_adjusted_overlap_reconciliation
-- name    : actuarial_f_gmp_adjusted_overlap_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:30:15.573222+00:00
-- url     : https://prove2.me/theorems/42b1c0af-13fd-4afe-98ec-1a47e4df21d9
-- title:
--   Hypothetical full-replacement overlap reconciliation
-- statement:
--   For the expressly hypothetical contract in which an estate guarantee replaces the complete survivor payment and all arbitrary survivor supplements on overlapping dates, direct EPV equals replacement EPV plus the overlap EPV. This is an algebraic identity for that defined contract. If the survivor supplements include statutory survivor GMP, the full-replacement contract is not the protected UK entitlement. The capstone uses the distinct protected survivor replacement, which retains statutory minima.
-- source:
--   Original derived hypothetical full-replacement finite EPV identity. Contractual overlap algebra is based on explicitly defined payment states and is not a statutory benefit rule. PSA 1993 section 17 protects survivor GMP, https://www.legislation.gov.uk/ukpga/1993/48/section/17 .

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpAdjustedDirectEPV
import Definitions.Def_actuarial_f_gmpAdjustedReplacementEPV
import Definitions.Def_actuarial_f_gmpAdjustedOverlapEPV

open ActuarialUnderpinsF

theorem actuarial_f_gmp_adjusted_overlap_reconciliation
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (survivorSupplement : ℕ → ℕ → ℕ → ℕ → ℝ) :
    gmpAdjustedDirectEPV n h r g p disc a b c sa sb estate
      ga gb gc gs ge memberSupplement survivorSupplement =
    gmpAdjustedReplacementEPV n h r g p disc a b c sa sb estate
      ga gb gc gs ge memberSupplement survivorSupplement +
    gmpAdjustedOverlapEPV n h r g p disc a b sa sb gs
      survivorSupplement := by
  sorry
