-- Prove2me | Theorems.Thm_exp_le_exp_of_pow_le_pow
-- name    : exp_le_exp_of_pow_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:42.596388+00:00
-- url     : https://prove2.me/theorems/4768fa84-e01e-4a7f-a34d-45c65c5b1b32
-- title:
--   exp le exp of pow le pow: exp le exp of pow le pow
-- statement:
--   The exp le exp of pow le pow construction uses the exp le exp of pow le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L45-L47
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L45-L47

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem exp_le_exp_of_pow_le_pow (a : Γ₀) (hlt : a < 1) (h₀ : a ≠ 0) {n m : ℤ} (hle : a ^ n ≤ a ^ m) :
    m ≤ n := by sorry
