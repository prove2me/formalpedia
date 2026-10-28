-- Prove2me | Theorems.Thm_actuarial_f_member_two_tranche_calendar_payment
-- name    : actuarial_f_member_two_tranche_calendar_payment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:25:12.016173+00:00
-- url     : https://prove2.me/theorems/a2186e61-51b7-4b5d-8719-ec0063916814
-- title:
--   Four-stream monthly cashflow identity
-- statement:
--   Expand the elected member first tranche, independent second tranche, linked survivor and estate amount at a date.
--
--   The asserted result is:
--
--   $$
--   C_t=C^{(1)}_t+C^{(2)}_t+C^S_t+C^E_t
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_linkedSpouseBasis
import Definitions.Def_actuarial_f_linkedFirstTranche
import Definitions.Def_actuarial_f_monthlyLinkedInstalment

open ActuarialUnderpinsF

theorem actuarial_f_member_two_tranche_calendar_payment
    (h r g z i j t : ℕ) (a b c : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (estate ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) :
    monthlyLinkedInstalment h r g z i j t
        a b c sa sb estate ga gb gc gs ge =
      linkedFirstTranche r z i t a b ga gb +
      c z * gc t * memberDue r i t +
      spouseInstalment h z i j t (linkedSpouseBasis a b sa sb) gs +
      estateInstalment h r g z i t estate ge := by
  sorry
