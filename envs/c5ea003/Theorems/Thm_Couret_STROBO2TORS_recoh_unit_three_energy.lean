-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_unit_three_energy
-- name    : Couret.STROBO2TORS.recoh_unit_three_energy
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:53.271498+00:00
-- url     : https://prove2.me/theorems/869148ed-f1fe-4374-a138-19ac10f95c4a
-- title:
--   Norm expansion for three unit phases
-- statement:
--   If $a,b,c\in\mathbb C$ have modulus one, then
--
--   $$|a+b+c|^2=3+2\operatorname{Re}(a\overline b+a\overline c+b\overline c).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerAverage.lean#L147-L164, lines 147–164; source file SHA-256 82ee1df9b270ad5f4eb67127defb17a17528059f12fe33954ce8f77aa29140c7; theorem Couret.STROBO2TORS.recoh_unit_three_energy

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

theorem recoh_unit_three_energy (a b c : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ‖a + b + c‖ ^ 2 =
      3 + 2 * ((a * star b).re + (a * star c).re + (b * star c).re) := by sorry




















end Couret.STROBO2TORS
