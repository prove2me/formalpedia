-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_energy_eq_one_of_opposite
-- name    : Couret.STROBO2TORS.recoh_odd_power_energy_eq_one_of_opposite
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:32.408751+00:00
-- url     : https://prove2.me/theorems/4862c816-7483-4bea-87ce-a4bdff503e2b
-- title:
--   An opposite pair leaves unit odd-power energy
-- statement:
--   For $a,b,c\in\mathbb C$ put $E_j=|a^{2j+1}+b^{2j+1}+c^{2j+1}|^2$. Assume $|a|=|b|=|c|=1$ and at least one of $a=-b$, $a=-c$, $b=-c$. For every $j\in\mathbb N$,
--
--   $$E_j=1.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerAverage.lean#L241-L262, lines 241–262; source file SHA-256 82ee1df9b270ad5f4eb67127defb17a17528059f12fe33954ce8f77aa29140c7; theorem Couret.STROBO2TORS.recoh_odd_power_energy_eq_one_of_opposite

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
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

theorem recoh_odd_power_energy_eq_one_of_opposite (a b c : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hop : RecohHasOppositePair a b c) (j : ℕ) :
    recohOddPowerEnergy a b c j = 1 := by sorry








end Couret.STROBO2TORS
