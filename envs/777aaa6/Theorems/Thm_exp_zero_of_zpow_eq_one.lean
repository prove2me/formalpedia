-- Prove2me | Theorems.Thm_exp_zero_of_zpow_eq_one
-- name    : exp_zero_of_zpow_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:45:13.271575+00:00
-- url     : https://prove2.me/theorems/df589427-a842-4163-951d-b888cfa1a05e
-- title:
--   exp zero of zpow eq one: exp zero of zpow eq one
-- statement:
--   The exp zero of zpow eq one construction uses the exp zero of zpow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L68-L76
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L68-L76

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem exp_zero_of_zpow_eq_one {a : Γ₀} (h : a < 1) {n : ℤ} (han : a ^ n = 1) : n = 0 := by sorry
