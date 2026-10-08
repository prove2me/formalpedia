-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_actual_HasSum_and_absolute
-- name    : ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-04T13:44:29.816983+00:00
-- url     : https://prove2.me/theorems/bb7477e4-5539-4015-b8cf-9bad57e1c8a0
-- title:
--   The selected integer output has its genuine sum and absolute convergence
-- statement:
--   For every even n>=2 and integers b,a, the actual selected rational quartic multiplier has a genuine HasSum of weightedR at all positive integers, equal to b+a*zetaReal(9), and its absolute norms are Summable. Both conclusions are derived from the complete actual source proof closure, with no HasSum or summability premise.
-- source:
--   Actual frozen native CoefficientMapMatrix source SHA256 a4bf1766c8bbcc1f2f83af27594ba10b3dfcd4e55058f10ccc4d4b25cb9c6d99

import Definitions.Def_ZetaNine_CoefficientMapMatrix

set_option autoImplicit false
open scoped BigOperators Matrix
open Polynomial ZetaNine ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapKernelBridge

theorem ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
      ((t + 1 : ℕ) : ℚ) : ℝ))
        ((b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖):= by sorry
