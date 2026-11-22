-- Prove2me | Theorems.Thm_P2M_exp_zero_of_zpow_eq_one__f6bf2bc7dd54
-- name    : P2M_exp_zero_of_zpow_eq_one__f6bf2bc7dd54
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:42:11.191801+00:00
-- url     : https://prove2.me/theorems/beab690a-0325-4f19-98fd-bf44461cb270
-- title:
--   P2 M exp zero of zpow eq one  f6bf2bc7dd54: P2 M exp zero of zpow eq one  f6bf2bc7dd54
-- statement:
--   The P2 M exp zero of zpow eq one  f6bf2bc7dd54 construction uses the P2 M exp zero of zpow eq one  f6bf2bc7dd54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L54-L66
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L54-L66

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem P2M_exp_zero_of_zpow_eq_one__f6bf2bc7dd54 {n : ℤ} (ha : (0 : Γ₀) ^ n = 1) : n = 0 := by sorry

alias «exp_zero_of_zpow_eq_one'» := P2M_exp_zero_of_zpow_eq_one__f6bf2bc7dd54
