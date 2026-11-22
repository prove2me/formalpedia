-- Prove2me | solution 1 for exp_le_exp_of_pow_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:41:44.694321+00:00
-- url     : https://prove2.me/submissions/4823ecc0-4d20-4e19-aadb-0bb513d218c1

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
theorem _root_.solution (a : Γ₀) (hlt : a < 1) (h₀ : a ≠ 0) {n m : ℤ} (hle : a ^ n ≤ a ^ m) :
    m ≤ n := by
  rwa [zpow_le_zpow_iff_right_of_lt_one₀ (zero_lt_iff.mpr h₀) hlt] at hle
