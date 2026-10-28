-- Prove2me | Theorems.Thm_actuarial_f_member_contingent_bridge_stops_at_death
-- name    : actuarial_f_member_contingent_bridge_stops_at_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:24:36.346165+00:00
-- url     : https://prove2.me/theorems/7212902c-b3d0-4340-9365-0391d7fd4602
-- title:
--   Member bridge stops after death
-- statement:
--   A member-contingent temporary bridge is zero on dates after the member terminal due index.
--
--   The asserted result is:
--
--   $$
--   t>i\Longrightarrow C^{\mathrm{bridge}}_t=0
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberContingentBridge

open ActuarialUnderpinsF

theorem actuarial_f_member_contingent_bridge_stops_at_death
    (r i start stop t : ℕ) (amount : ℝ) (hi : i < t) :
    memberContingentBridge r i start stop t amount = 0 := by
  sorry
