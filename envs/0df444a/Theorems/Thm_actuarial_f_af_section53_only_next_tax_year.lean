-- Prove2me | Theorems.Thm_actuarial_f_af_section53_only_next_tax_year
-- name    : actuarial_f_af_section53_only_next_tax_year
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:36:51.405989+00:00
-- url     : https://prove2.me/theorems/ebb86528-784f-4cc0-89e9-6ce63d569e7b
-- title:
--   Earlier non-statutory credits are only for next year
-- statement:
--   Conditional next-tax-year section 53 credit. Pension-credit-attributable pensions are excluded. All credit amounts and section 51/109 allocation eligibility require separate certification. The declared Lean statement is open.
-- source:
--   Pensions Act 1995 section 53(1)-(3A): https://www.legislation.gov.uk/ukpga/1995/26/section/53

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afSection53NextYearCredit

open ActuarialUnderpinsF

theorem actuarial_f_af_section53_only_next_tax_year
    (given required : ℕ) (credit : ℝ) (pensionCredit : Bool)
    (h : required ≠ given + 1) :
    afSection53NextYearCredit given required pensionCredit credit = 0 := by
  sorry
