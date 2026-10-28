-- Prove2me | Theorems.Thm_actuarial_f_survivor_parallel_respects_floor
-- name    : actuarial_f_survivor_parallel_respects_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:31:27.070376+00:00
-- url     : https://prove2.me/theorems/076432ec-32f6-4483-bf8d-0f3d85d26d3e
-- title:
--   Contractual spouse and statutory GMP floors are preserved
-- statement:
--   Contractual spouse and statutory GMP floors are preserved. This is a proof obligation on the exact declared Lean benefit contract. It does not certify scheme-specific legal inputs.
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpProtectedSurvivorParallel

open ActuarialUnderpinsF

theorem actuarial_f_survivor_parallel_respects_floor
    (scheme statutory : ℝ) :
    statutory ≤ gmpProtectedSurvivorParallel scheme statutory := by
  sorry
