-- Prove2me | Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
-- name    : Couret_RecohOddPowerAverage_39ee40b78d83
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:20.869372+00:00
-- url     : https://prove2.me/theorems/56dbe4f0-8002-4203-8b5c-df0f8b9314ba
-- title:
--   Odd-power energies and labelled phase-pair counts
-- statement:
--   For arbitrary complex phases a,b,c and a natural index j, recohOddPowerEnergy is the squared norm of a^(2j+1)+b^(2j+1)+c^(2j+1), a real number. RecohHasOppositePair is the disjunction a=-b or a=-c or b=-c. The real pair correlation recohOddPairCorrelation(a,b) is the equality indicator minus the opposite indicator. The natural counts recohEqualPhasePairs and recohOppositePhasePairs sum the corresponding indicators over the three labelled unordered pairs (a,b),(a,c),(b,c), retaining multiplicity when phase values coincide. These definitions assume neither unit norms nor an even-order root condition. In particular, at a=b=0 both pair indicators are one and their correlation is zero. The bundle does not contain the averaging inequalities.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohOddPowerAverage.lean; source file SHA-256 82ee1df9b270ad5f4eb67127defb17a17528059f12fe33954ce8f77aa29140c7

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

/-- The squared magnitude of the three-phase reading at the `j`th odd
exponent.  It is an analytic quantity, not a floating-point calculation. -/
noncomputable def recohOddPowerEnergy (a b c : ℂ) (j : ℕ) : ℝ :=
  ‖a ^ (2 * j + 1) + b ^ (2 * j + 1) + c ^ (2 * j + 1)‖ ^ 2

/-- An opposite pair among the three labelled phases. -/
def RecohHasOppositePair (a b c : ℂ) : Prop :=
  a = -b ∨ a = -c ∨ b = -c

/-- The contribution of a pair to odd-power orthogonality. -/
noncomputable def recohOddPairCorrelation (a b : ℂ) : ℝ := by
  classical
  exact (if a = b then 1 else 0) - (if a = -b then 1 else 0)

/-- Number of equal unordered pairs of labelled phases, retaining multiplicity. -/
noncomputable def recohEqualPhasePairs (a b c : ℂ) : ℕ := by
  classical
  exact (if a = b then 1 else 0) + (if a = c then 1 else 0) +
    (if b = c then 1 else 0)

/-- Number of opposite unordered pairs of labelled phases, retaining multiplicity. -/
noncomputable def recohOppositePhasePairs (a b c : ℂ) : ℕ := by
  classical
  exact (if a = -b then 1 else 0) + (if a = -c then 1 else 0) +
    (if b = -c then 1 else 0)

































end Couret.STROBO2TORS


