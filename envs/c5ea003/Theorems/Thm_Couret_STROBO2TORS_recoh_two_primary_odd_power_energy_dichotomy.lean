-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_odd_power_energy_dichotomy
-- name    : Couret.STROBO2TORS.recoh_two_primary_odd_power_energy_dichotomy
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:23.634548+00:00
-- url     : https://prove2.me/theorems/35526efa-5a5c-4671-a128-9fa6f2d90c9d
-- title:
--   Two-primary specialization of the odd-power energy dichotomy
-- statement:
--   For $a,b,c\in\mathbb C$ put $E_j=|a^{2j+1}+b^{2j+1}+c^{2j+1}|^2$. Let $n\in\mathbb N$ and $a^{2^{n+1}}=b^{2^{n+1}}=c^{2^{n+1}}=1$. Then
--
--   $$\bigl(\forall j\in\mathbb N,\ E_j=1\bigr)\quad\text{or}\quad\exists j<2^n:\ E_j\ge3.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerAverage.lean#L296-L308, lines 296–308; source file SHA-256 82ee1df9b270ad5f4eb67127defb17a17528059f12fe33954ce8f77aa29140c7; theorem Couret.STROBO2TORS.recoh_two_primary_odd_power_energy_dichotomy

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_energy_dichotomy
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

theorem recoh_two_primary_odd_power_energy_dichotomy
    (depth : ℕ) (a b c : ℂ)
    (ha : a ^ (2 ^ (depth + 1)) = 1)
    (hb : b ^ (2 ^ (depth + 1)) = 1)
    (hc : c ^ (2 ^ (depth + 1)) = 1) :
    (∀ j : ℕ, recohOddPowerEnergy a b c j = 1) ∨
      ∃ j < 2 ^ depth, 3 ≤ recohOddPowerEnergy a b c j := by sorry


end Couret.STROBO2TORS
