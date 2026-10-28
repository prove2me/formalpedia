-- Prove2me | Theorems.Thm_actuarial_f_elected_spouse_follows_option_a
-- name    : actuarial_f_elected_spouse_follows_option_a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:24:56.056018+00:00
-- url     : https://prove2.me/theorems/95adad9a-4ed7-452f-8cf1-efd364af50ac
-- title:
--   Option A carries its spouse entitlement
-- statement:
--   When A exceeds B at award, the linked survivor basis follows A, even if B separately promises a higher survivor amount.
--
--   The asserted result is:
--
--   $$
--   A_z>B_z\Longrightarrow S_{zi}=S^A_{zi}
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_linkedSpouseBasis

open ActuarialUnderpinsF

theorem actuarial_f_elected_spouse_follows_option_a
    (a b : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (z i : ℕ) (hab : b z < a z) :
    linkedSpouseBasis a b sa sb z i = sa z i := by
  sorry
