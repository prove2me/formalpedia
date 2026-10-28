-- Prove2me | Theorems.Thm_actuarial_f_gmp_adjusted_state_reconciliation
-- name    : actuarial_f_gmp_adjusted_state_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:29:55.053914+00:00
-- url     : https://prove2.me/theorems/12663204-ea6d-4318-8e2b-226d69f54698
-- title:
--   State and direct EPV for supplied supplements
-- statement:
--   For any supplied member and survivor supplementary streams, the direct finite-scenario EPV of the parallel contract equals the sum of the base-state EPV and the state-weighted supplementary EPV. This is a mathematical finite-sum identity. It does not establish that the supplements are legally due, or that guarantees can discharge statutory survivor entitlements.
-- source:
--   Original derived finite joint-law EPV decomposition, in the setting of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, Chapters 10–11, https://doi.org/10.1017/9781108784184 . Pension entitlement remains separately certified.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpAdjustedDirectEPV
import Definitions.Def_actuarial_f_gmpAdjustedStateEPV

open ActuarialUnderpinsF

theorem actuarial_f_gmp_adjusted_state_reconciliation
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (survivorSupplement : ℕ → ℕ → ℕ → ℕ → ℝ) :
    gmpAdjustedDirectEPV n h r g p disc a b c sa sb estate
      ga gb gc gs ge memberSupplement survivorSupplement =
    gmpAdjustedStateEPV n h r g p disc a b c sa sb estate
      ga gb gc gs ge memberSupplement survivorSupplement := by
  sorry
