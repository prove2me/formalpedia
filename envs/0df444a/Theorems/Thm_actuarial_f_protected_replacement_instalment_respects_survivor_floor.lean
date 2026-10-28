-- Prove2me | Theorems.Thm_actuarial_f_protected_replacement_instalment_respects_survivor_floor
-- name    : actuarial_f_protected_replacement_instalment_respects_survivor_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:33:04.961563+00:00
-- url     : https://prove2.me/theorems/8c6e4b86-f165-4190-a5fa-a72910efd1e6
-- title:
--   Entire protected guarantee instalment respects survivor statutory minimum
-- statement:
--   Entire protected guarantee instalment respects survivor statutory minimum. This is a proof obligation on the exact declared Lean benefit contract. It does not certify scheme-specific legal inputs.
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_linkedFirstTranche
import Definitions.Def_actuarial_f_gmpProtectedReplacementInstalment

open ActuarialUnderpinsF

theorem actuarial_f_protected_replacement_instalment_respects_survivor_floor
    (h r g z i j t : ℕ) (a b c : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (estate ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (statutorySurvivor : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hm : 0 ≤ linkedFirstTranche r z i t a b ga gb +
      c z * gc t * memberDue r i t + memberSupplement z i t +
        estateInstalment h r g z i t estate ge) :
    statutorySurvivor z i j t ≤
      gmpProtectedReplacementInstalment h r g z i j t a b c sa sb
        estate ga gb gc gs ge memberSupplement statutorySurvivor := by
  sorry
