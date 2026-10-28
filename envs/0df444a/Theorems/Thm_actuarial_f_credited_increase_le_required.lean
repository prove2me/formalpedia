-- Prove2me | Theorems.Thm_actuarial_f_credited_increase_le_required
-- name    : actuarial_f_credited_increase_le_required
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:32:53.672356+00:00
-- url     : https://prove2.me/theorems/32d62dcc-7eec-4b62-9fdb-c8053e695f68
-- title:
--   Credited ordinary increase cannot increase amount still due
-- statement:
--   Credited ordinary increase cannot increase amount still due. This is a proof obligation on the exact declared Lean benefit contract. It does not certify scheme-specific legal inputs.
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_pensionIncreaseOutstanding

open ActuarialUnderpinsF

theorem actuarial_f_credited_increase_le_required
    (required credited : ℝ) (h : 0 ≤ credited)
    (hr : 0 ≤ required) :
    pensionIncreaseOutstanding required credited ≤ required := by
  sorry
