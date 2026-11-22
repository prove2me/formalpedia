-- Prove2me | Theorems.Thm_Finset_prod_zpow_eq_zpow_sum
-- name    : Finset.prod_zpow_eq_zpow_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:45:26.417374+00:00
-- url     : https://prove2.me/theorems/b9faae59-1a22-4af5-bdc2-d7e7a3093667
-- title:
--   Finset: prod zpow eq zpow sum
-- statement:
--   The Finset construction uses the prod zpow eq zpow sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L103-L105
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L103-L105

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
open Finset
variable {ι α β : Type*} [CommGroupWithZero β]

theorem Finset.prod_zpow_eq_zpow_sum (s : Finset ι) (f : ι → ℤ) (a : β) (ha : a ≠ 0):
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by sorry
