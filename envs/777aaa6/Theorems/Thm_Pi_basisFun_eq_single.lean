-- Prove2me | Theorems.Thm_Pi_basisFun_eq_single
-- name    : Pi.basisFun_eq_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:45:21.707522+00:00
-- url     : https://prove2.me/theorems/2e2f8efb-b8d0-4069-a70a-fbc99bfb533e
-- title:
--   Pi: basis Fun eq single
-- statement:
--   The Pi construction uses the basis Fun eq single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L78-L80
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L78-L80

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem Pi.basisFun_eq_single {ι : Type*} [Finite ι] [DecidableEq ι] {R : Type*}
    [Semiring R] (i : ι) : Pi.basisFun R ι i = Pi.single i 1 := by sorry
