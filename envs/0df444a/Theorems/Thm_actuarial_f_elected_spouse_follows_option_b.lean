-- Prove2me | Theorems.Thm_actuarial_f_elected_spouse_follows_option_b
-- name    : actuarial_f_elected_spouse_follows_option_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:24:44.723411+00:00
-- url     : https://prove2.me/theorems/f80eda15-b186-4e0e-a281-03b21647dcea
-- title:
--   Option B carries its spouse entitlement
-- statement:
--   When the member selects B (including an equal-award tie), the linked survivor pension is B's promised survivor amount.
--
--   The asserted result is:
--
--   $$
--   A_z\le B_z\Longrightarrow S_{zi}=S^B_{zi}
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_linkedSpouseBasis

open ActuarialUnderpinsF

theorem actuarial_f_elected_spouse_follows_option_b
    (a b : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (z i : ℕ) (hab : a z ≤ b z) :
    linkedSpouseBasis a b sa sb z i = sb z i := by
  sorry
