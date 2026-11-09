-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_choice_energy_ge_one
-- name    : Couret.STROBO2TORS.recoh_odd_power_choice_energy_ge_one
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:36.207785+00:00
-- url     : https://prove2.me/theorems/0e7b668f-59e6-4c40-b6d6-cea66efb3da2
-- title:
--   Half-unit energy approximations select energy at least one
-- statement:
--   For a rational sequence $A_j$, search $j=0,\ldots,m-1$ for the first $A_j\ge3/2$, and let $c_m(A)$ be that index, or zero if none exists. Let $m>0$ and $e_j\in\mathbb R$. Suppose $|A_j-e_j|\le1/2$ for every $j<m$, and either all these $e_j$ equal one or some $e_j\ge3$. Then
--
--   $$e_{c_m(A)}\ge1.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerSelection.lean#L113-L140, lines 113–140; source file SHA-256 4b170d730a51729f5ba927507b15a30bb6589eba29b9066d779b320d2f7bf524; theorem Couret.STROBO2TORS.recoh_odd_power_choice_energy_ge_one

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

theorem recoh_odd_power_choice_energy_ge_one
    (m : ℕ) (hm : 0 < m) (energy : ℕ → ℝ) (approx : ℕ → ℚ)
    (hcert : ∀ j < m, |(approx j : ℝ) - energy j| ≤ (1 / 2 : ℝ))
    (hdich : (∀ j < m, energy j = 1) ∨ ∃ j < m, 3 ≤ energy j) :
    1 ≤ energy (recohOddPowerChoice m approx) := by sorry




























end Couret.STROBO2TORS
