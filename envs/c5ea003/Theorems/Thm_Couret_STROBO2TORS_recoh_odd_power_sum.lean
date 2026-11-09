-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_sum
-- name    : Couret.STROBO2TORS.recoh_odd_power_sum
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:28.029226+00:00
-- url     : https://prove2.me/theorems/42de9822-d807-48f3-811e-e72016e123f9
-- title:
--   Odd geometric sum over a full even period
-- statement:
--   Let $m\in\mathbb N$ and $z\in\mathbb C$ satisfy $z^{2m}=1$. Then
--
--   $$\sum_{j=0}^{m-1}z^{2j+1}=\begin{cases}m,&z=1,\\-m,&z=-1,\\0,&\text{otherwise}.\end{cases}$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerAverage.lean#L62-L82, lines 62–82; source file SHA-256 82ee1df9b270ad5f4eb67127defb17a17528059f12fe33954ce8f77aa29140c7; theorem Couret.STROBO2TORS.recoh_odd_power_sum

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

theorem recoh_odd_power_sum (m : ℕ) (z : ℂ)
    (hz : z ^ (2 * m) = 1) :
    (∑ j ∈ Finset.range m, z ^ (2 * j + 1)) =
      if z = 1 then (m : ℂ) else if z = -1 then -(m : ℂ) else 0 := by sorry






























end Couret.STROBO2TORS
