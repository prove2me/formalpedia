-- Prove2me | Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549
-- name    : Couret_RecohOddPowerSelection_49cfa1cd1549
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:41.697578+00:00
-- url     : https://prove2.me/theorems/f9b6ec1c-ac6f-4584-9336-a9d3e770d533
-- title:
--   Deterministic ordered selection of an odd exponent
-- statement:
--   Given rational approximations $a_j$, the list search returns the first listed index with $a_j\ge3/2$, or no result. Searching $0,\ldots,m-1$ and replacing failure by zero defines a choice $c$, with selected exponent $$e=2c+1.$$ The predicate version encodes true and false as rational values two and zero. The squared-norm version accepts an index when its supplied rational squared norm is at least $9/4$. These raw functions allow $m=0$, which falls back to $c=0$ and exponent one. They compute from the supplied approximations or predicate; any analytic guarantee, precision assumption or root interpretation is established separately.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerSelection.lean; source file SHA-256 4b170d730a51729f5ba927507b15a30bb6589eba29b9066d779b320d2f7bf524

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
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

/-- Search a list in its given order for a certified threshold candidate. -/
def recohOddPowerFind (approx : ℕ → ℚ) : List ℕ → Option ℕ
  | [] => none
  | j :: js =>
      if (3 / 2 : ℚ) ≤ approx j then some j else recohOddPowerFind approx js

/-- Select the first acceptable index from `0,...,m-1`, or zero on failure. -/
def recohOddPowerChoice (m : ℕ) (approx : ℕ → ℚ) : ℕ :=
  (recohOddPowerFind approx (List.range m)).getD 0

/-- The multiplier to place in the character descriptor. -/
def recohOddPowerSelectedExponent (m : ℕ) (approx : ℕ → ℚ) : ℕ :=
  2 * recohOddPowerChoice m approx + 1



















/-- The same ordered search with an arbitrary computable acceptance test.
The values two and zero encode success and failure for the rational search;
the resulting comparisons have no analytic or approximate inputs. -/
def recohOddPredicateChoice (m : ℕ) (accept : ℕ → Bool) : ℕ :=
  recohOddPowerChoice m (fun j => if accept j then 2 else 0)











/-- Search using rational squared norms of complex approximation centres.
The calculation compares to `9/4` and never evaluates a square root. -/
def recohOddSquaredChoice (m : ℕ) (sqNorm : ℕ → ℚ) : ℕ :=
  recohOddPredicateChoice m (fun j => decide ((9 / 4 : ℚ) ≤ sqNorm j))









end Couret.STROBO2TORS


