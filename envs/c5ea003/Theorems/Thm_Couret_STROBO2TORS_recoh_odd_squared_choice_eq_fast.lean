-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_odd_squared_choice_eq_fast
-- name    : Couret.STROBO2TORS.recoh_odd_squared_choice_eq_fast
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:39.855225+00:00
-- url     : https://prove2.me/theorems/e852052c-3016-47c8-8ab3-145129ee4d92
-- title:
--   Fast squared-norm selection preserves the specified answer
-- statement:
--   For every natural $m$ and rational squared-norm sequence $s$, list and counter search return the same first index $j<m$ with $s_j\ge9/4$, or zero if absent.
--
--   These are equalities of the public functions on their entire domains.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerRuntime.lean#L73-L77, lines 73–77; source file SHA-256 68f6c0865f66d96b40c799d0944d0bcb5663a26041e40b6e3ea290ce793e89bf; theorem Couret.STROBO2TORS.recoh_odd_squared_choice_eq_fast

import Definitions.Def_Couret_RecohOddPowerRuntime_8c8d44664d18
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549

set_option autoImplicit false

/-!
# Certified short-circuit execution of the odd-power selector

The mathematical selector is specified using `List.range`.  Constructing
that list before searching would allocate the whole search interval even
when its first index succeeds.  The implementation below instead carries
the current index and the remaining number of candidates.  Its recursive
call is reached only after the current candidate fails.

The equivalence with the list specification is proved for every start
and count.  Compiler simplification also replaces the public wrappers,
which were compiled before this module introduced the replacement.
The search order, inclusive thresholds, and zero fallback are unchanged.
-/

namespace Couret.STROBO2TORS

@[csimp] theorem recoh_odd_squared_choice_eq_fast :
    @recohOddSquaredChoice = @recohOddSquaredChoiceFast := by sorry


end Couret.STROBO2TORS
