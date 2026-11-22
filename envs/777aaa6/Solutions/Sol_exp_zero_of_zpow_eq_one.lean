-- Prove2me | solution 1 for exp_zero_of_zpow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:56:53.864809+00:00
-- url     : https://prove2.me/submissions/ecbf32dc-d22e-4a49-9802-5490bae22284

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
import Theorems.Thm_exp_le_exp_of_pow_le_pow
import Theorems.Thm_P2M_exp_zero_of_zpow_eq_one__f6bf2bc7dd54

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
theorem _root_.solution {a : Γ₀} (h : a < 1) {n : ℤ} (han : a ^ n = 1) : n = 0 := by
  by_cases ha : a = 0
  · subst ha
    exact exp_zero_of_zpow_eq_one' han
  · apply le_antisymm
    · apply exp_le_exp_of_pow_le_pow a h ha
      simp [han]
    · apply exp_le_exp_of_pow_le_pow a h ha
      simp [han]
