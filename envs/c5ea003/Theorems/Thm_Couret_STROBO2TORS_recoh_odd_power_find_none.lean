-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_find_none
-- name    : Couret.STROBO2TORS.recoh_odd_power_find_none
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:51:42.569399+00:00
-- url     : https://prove2.me/theorems/d3c7c2df-fdfe-48c6-972d-226b987340c0
-- title:
--   A failed threshold search excludes every passing list member
-- statement:
--   For any rational sequence $A$ and finite index list $L$,
--
--   $$\operatorname{find}(A,L)=\mathrm{none}\Longrightarrow\forall j\in L,\ A_j<3/2.$$
--
--   The search returns the first index meeting the threshold $3/2$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerSelection.lean#L54-L69, lines 54–69; source file SHA-256 4b170d730a51729f5ba927507b15a30bb6589eba29b9066d779b320d2f7bf524; theorem Couret.STROBO2TORS.recoh_odd_power_find_none

import Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
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

theorem recoh_odd_power_find_none (approx : ℕ → ℚ) (js : List ℕ) :
    recohOddPowerFind approx js = none →
      ∀ j ∈ js, approx j < (3 / 2 : ℚ) := by sorry






































end Couret.STROBO2TORS
