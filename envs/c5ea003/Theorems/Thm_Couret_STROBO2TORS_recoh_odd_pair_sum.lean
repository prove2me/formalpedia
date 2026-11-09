-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_odd_pair_sum
-- name    : Couret.STROBO2TORS.recoh_odd_pair_sum
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:07.035039+00:00
-- url     : https://prove2.me/theorems/42a528d1-d320-4ec2-94fe-99208b52f1f6
-- title:
--   Odd-power pair correlation sum
-- statement:
--   Write $C(a,b)=[a=b]-[a=-b]$, with real indicator values, and let $N_{=}$ and $N_{-}$ count equal and opposite pairs among the three indexed pairs $(a,b),(a,c),(b,c)$. Let $m\in\mathbb N$, $a^{2m}=b^{2m}=1$ and $|b|=1$. Then
--
--   $$\sum_{j=0}^{m-1}\operatorname{Re}((a\overline b)^{2j+1})=mC(a,b).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerAverage.lean#L113-L145, lines 113–145; source file SHA-256 82ee1df9b270ad5f4eb67127defb17a17528059f12fe33954ce8f77aa29140c7; theorem Couret.STROBO2TORS.recoh_odd_pair_sum

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_sum
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

theorem recoh_odd_pair_sum (m : ℕ) (a b : ℂ)
    (ha : a ^ (2 * m) = 1) (hb : b ^ (2 * m) = 1)
    (hbn : ‖b‖ = 1) :
    (∑ j ∈ Finset.range m, ((a * star b) ^ (2 * j + 1)).re) =
      (m : ℝ) * recohOddPairCorrelation a b := by sorry






















end Couret.STROBO2TORS
