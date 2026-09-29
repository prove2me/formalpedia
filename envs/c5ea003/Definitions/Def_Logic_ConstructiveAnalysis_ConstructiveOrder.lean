-- Prove2me | Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveOrder
-- name    : Logic_ConstructiveAnalysis_ConstructiveOrder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:52:43.217898+00:00
-- url     : https://prove2.me/theorems/0bc8e8d4-9c21-489b-b3a0-cc687f2f9f65
-- title:
--   Aether Catalog definitions — Logic_ConstructiveAnalysis_ConstructiveOrder
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ConstructiveAnalysis.ConstructiveOrder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ConstructiveAnalysis/ConstructiveOrder.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
/-
# The constructive order on Bishop reals

Constructively, the order relation on the reals is *not* obtained by negating an
equality: `x < y` must carry positive information.  Bishop defines, for regular
sequences of rationals,

  `x > 0`  iff  `∃ n, x n > 1/n`,      `x < y`  iff  `y - x > 0`,

so that a proof of `x < y` is a *witness index* together with a rational
inequality, from which a rational lower bound on the gap `y - x` can be read off.

This file develops that order for the Bishop reals of
`Logic/ConstructiveAnalysis/BishopReals.lean`:

* `Bishop.Reg.pos_iff_toReal_pos`, `Bishop.Reg.lt_iff_toReal_lt` : the witnessed
  relations agree with the classical order on the denoted reals (so nothing is
  lost, and the constructive relation is not weaker);
* `Bishop.Reg.lt_cotrans` : **cotransitivity**, the constructive substitute for
  trichotomy, in fully explicit form — from a witness `n` for `x < y` one computes
  an index `m` at which a *decidable rational comparison* of `z.approx m` with the
  midpoint `(x.approx m + y.approx m)/2` decides between `x < z` and `z < y`;
* `Bishop.Reg.approx_locate_left`, `approx_locate_right`, `approx_locate` : the
  constructive location lemma — for rationals `a < b`, a single rational
  comparison at a computed index decides `a < x` or `x < b`;
* `Bishop.Reg.no_uniform_lt_witness` : the witness index in `x < y` cannot be
  bounded in advance — the precise sense in which the order, though it agrees
  extensionally with the classical one, is not decidable at bounded precision.
-/


namespace Bishop

namespace Reg

/-! ## Two-sided form of the explicit modulus -/




/-! ## Positivity and the strict order -/

/-- **Bishop positivity**: `x > 0` means that some approximation exceeds its own
error bound.  A proof is a witness index `n`, from which the rational number
`x.approx n - 1/(n+1) > 0` is an explicit lower bound for `x`. -/
def Pos (x : Reg) : Prop := ∃ n : ℕ, 1 / (n + 1 : ℚ) < x.approx n

/-- **Bishop's strict order**: `x < y` means that at some index the approximations
are separated by more than the sum of their error bounds. -/
def Lt (x y : Reg) : Prop := ∃ n : ℕ, x.approx n + 2 / (n + 1 : ℚ) < y.approx n






/-- The rational gap read off from a witness for `x < y`. -/
def gapAt (x y : Reg) (n : ℕ) : ℚ := y.approx n - x.approx n - 2 / (n + 1)






/-! ## Locating a Bishop real between two rationals -/




/-! ## The order is not decidable at bounded precision -/


end Reg

end Bishop


