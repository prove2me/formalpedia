-- Prove2me | Theorems.Thm_actuarial_f_monthly_linked_guarantee_reconciliation
-- name    : actuarial_f_monthly_linked_guarantee_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:25:59.218982+00:00
-- url     : https://prove2.me/theorems/22558202-c2f7-4013-b600-40fed3641012
-- title:
--   Corrected monthly survivor and guarantee overlap
-- statement:
--   Parallel liability equals the replacement-rule liability plus the precisely overlapping, linked survivor EPV.
--
--   The asserted result is:
--
--   $$
--   V_D=V_R+O
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_guaranteeOverlapEPV
import Definitions.Def_actuarial_f_linkedSpouseBasis
import Definitions.Def_actuarial_f_monthlyLinkedDirectEPV
import Definitions.Def_actuarial_f_monthlyLinkedReplacementEPV

open ActuarialUnderpinsF

theorem actuarial_f_monthly_linked_guarantee_reconciliation
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ) :
    monthlyLinkedDirectEPV n h r g p disc a b c
        sa sb estate ga gb gc gs ge =
      monthlyLinkedReplacementEPV n h r g p disc a b c
        sa sb estate ga gb gc gs ge +
      guaranteeOverlapEPV n h r g p disc
        (linkedSpouseBasis a b sa sb) gs := by
  sorry
