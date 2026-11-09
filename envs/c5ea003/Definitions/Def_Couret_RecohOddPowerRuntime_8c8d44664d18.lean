-- Prove2me | Definitions.Def_Couret_RecohOddPowerRuntime_8c8d44664d18
-- name    : Couret_RecohOddPowerRuntime_8c8d44664d18
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:08.036866+00:00
-- url     : https://prove2.me/theorems/9cf97fab-a53a-4a97-90df-8b6c146a7d76
-- title:
--   Sequential search for an acceptable odd-power index
-- statement:
--   Defines a recursive search over count consecutive indices beginning at start. It returns none at count zero; otherwise it accepts the current index when the rational approximation is at least 3/2 and recurses only after failure. ChoiceFast searches indices 0 through m−1 and returns zero if none is accepted; SelectedExponentFast returns twice that choice plus one. PredicateChoiceFast substitutes rational values two and zero for a Boolean predicate, and SquaredChoiceFast accepts rational squared norms at least 9/4. All thresholds are inclusive; m=0 produces choice zero and exponent one.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerRuntime.lean; source file SHA-256 68f6c0865f66d96b40c799d0944d0bcb5663a26041e40b6e3ea290ce793e89bf

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

/-- Inspect one candidate at a time, without constructing the remaining range. -/
def recohOddPowerFindFrom (approx : ℕ → ℚ) (start : ℕ) : ℕ → Option ℕ
  | 0 => none
  | count + 1 =>
      if (3 / 2 : ℚ) ≤ approx start then some start
      else recohOddPowerFindFrom approx (start + 1) count



/-- Runtime implementation of the first acceptable index, with zero fallback. -/
def recohOddPowerChoiceFast (m : ℕ) (approx : ℕ → ℚ) : ℕ :=
  (recohOddPowerFindFrom approx 0 m).getD 0



/-- Runtime wrapper for the odd character exponent. -/
def recohOddPowerSelectedExponentFast (m : ℕ) (approx : ℕ → ℚ) : ℕ :=
  2 * recohOddPowerChoiceFast m approx + 1



/-- Runtime wrapper for a certified Boolean acceptance predicate. -/
def recohOddPredicateChoiceFast (m : ℕ) (accept : ℕ → Bool) : ℕ :=
  recohOddPowerChoiceFast m (fun j => if accept j then 2 else 0)



/-- Runtime wrapper for the rational squared-norm test. -/
def recohOddSquaredChoiceFast (m : ℕ) (sqNorm : ℕ → ℚ) : ℕ :=
  recohOddPredicateChoiceFast m (fun j => decide ((9 / 4 : ℚ) ≤ sqNorm j))



end Couret.STROBO2TORS


