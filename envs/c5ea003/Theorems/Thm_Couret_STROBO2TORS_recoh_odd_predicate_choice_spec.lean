-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_odd_predicate_choice_spec
-- name    : Couret.STROBO2TORS.recoh_odd_predicate_choice_spec
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:44.522938+00:00
-- url     : https://prove2.me/theorems/311f5d34-194a-4a3f-a840-c3c89db5e13d
-- title:
--   The Boolean selector passes or defaults after complete rejection
-- statement:
--   For a Boolean predicate $b$ on natural indices, let $c_m(b)$ be the first accepted index below $m$, defaulting to zero when none exists. For every $m\in\mathbb N$,
--
--   $$b(c_m(b))=\mathrm{true}\quad\text{or}\quad\bigl(c_m(b)=0\text{ and }\forall j<m,\ b(j)=\mathrm{false}\bigr).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerSelection.lean#L182-L208, lines 182–208; source file SHA-256 4b170d730a51729f5ba927507b15a30bb6589eba29b9066d779b320d2f7bf524; theorem Couret.STROBO2TORS.recoh_odd_predicate_choice_spec

import Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_find_none
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_find_some
import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

/-!
# Deterministic certified selection of an odd power

The executable search examines the rational approximations in ascending
index order, accepts the first value at least `3/2`, and falls back to index
zero.  Index `j` represents the odd character power `2*j+1`.

The contract uses an absolute error at most `1/2` on squared magnitude.
The root equations imply the dichotomy required to justify the fallback;
the selector never needs the hidden phases or an opposite-pair witness.
Constructing the rational approximations from a canonical square is a
separate obligation.  Extensionality below states the precise interface
that such a deterministic approximation procedure must satisfy.
-/

namespace Couret.STROBO2TORS

theorem recoh_odd_predicate_choice_spec (m : ℕ) (accept : ℕ → Bool) :
    accept (recohOddPredicateChoice m accept) = true ∨
      (recohOddPredicateChoice m accept = 0 ∧ ∀ j < m, accept j = false) := by sorry


















end Couret.STROBO2TORS
