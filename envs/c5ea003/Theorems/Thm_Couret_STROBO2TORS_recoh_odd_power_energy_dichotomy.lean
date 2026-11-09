-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_energy_dichotomy
-- name    : Couret.STROBO2TORS.recoh_odd_power_energy_dichotomy
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:03:57.981751+00:00
-- url     : https://prove2.me/theorems/2b86a1e0-9b8b-4a39-9f79-b4f4206b7111
-- title:
--   Odd-power energies are all one or one is at least three
-- statement:
--   For $a,b,c\in\mathbb C$ put $E_j=|a^{2j+1}+b^{2j+1}+c^{2j+1}|^2$. Let $m\in\mathbb N$ be positive and suppose $a^{2m}=b^{2m}=c^{2m}=1$. Then
--
--   $$\bigl(\forall j\in\mathbb N,\ E_j=1\bigr)\quad\text{or}\quad\exists j<m:\ E_j\ge3.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerAverage.lean#L278-L294, lines 278–294; source file SHA-256 82ee1df9b270ad5f4eb67127defb17a17528059f12fe33954ce8f77aa29140c7; theorem Couret.STROBO2TORS.recoh_odd_power_energy_dichotomy

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_energy_eq_one_of_opposite
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_energy_sum_ge
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Averaging odd powers of three roots of even order

The order is written `2 * m`, with `0 < m`.  This includes the entire
2-primary case and keeps the geometric-sum argument independent of a
particular presentation of the order.  Repeated complex phases are allowed.

The energy at index `j` is the squared norm of the reading at exponent
`2 * j + 1`.  An opposite pair makes every such energy equal to one.
Otherwise their sum is at least `3 * m`, and some energy is at least three.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

theorem recoh_odd_power_energy_dichotomy (m : ℕ) (hm : 0 < m) (a b c : ℂ)
    (ha : a ^ (2 * m) = 1) (hb : b ^ (2 * m) = 1)
    (hc : c ^ (2 * m) = 1) :
    (∀ j : ℕ, recohOddPowerEnergy a b c j = 1) ∨
      ∃ j < m, 3 ≤ recohOddPowerEnergy a b c j := by sorry




end Couret.STROBO2TORS
