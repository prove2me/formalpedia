-- Prove2me | Theorems.Thm_exp_zero_of_pow_eq_one_aux
-- name    : exp_zero_of_pow_eq_one_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:42:13.961119+00:00
-- url     : https://prove2.me/theorems/4b3fc9b5-09bd-48e3-82e8-b9dfa1598f34
-- title:
--   exp zero of pow eq one aux: exp zero of pow eq one aux
-- statement:
--   The exp zero of pow eq one aux construction uses the exp zero of pow eq one aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L49-L52
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L49-L52

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem exp_zero_of_pow_eq_one_aux {n : ℕ} (ha : (0 : Γ₀) ^ n = 1) : n = 0 := by sorry
