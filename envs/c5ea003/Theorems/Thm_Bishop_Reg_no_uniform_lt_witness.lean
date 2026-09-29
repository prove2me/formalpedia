-- Prove2me | Theorems.Thm_Bishop_Reg_no_uniform_lt_witness
-- name    : Bishop.Reg.no_uniform_lt_witness
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:18:05.049879+00:00
-- url     : https://prove2.me/theorems/aff30f3e-65fb-4521-9d5c-587f94867d10
-- title:
--   No uniform witness bound.
-- statement:
--   **No uniform witness bound.**  However large a precision `N` is fixed in advance,
--   there are Bishop reals with `x < y` for which no index `n ≤ N` witnesses the
--   inequality: the witness in `Lt` genuinely depends on the pair, so the order cannot
--   be decided by inspecting a bounded number of approximations.  This is the exact
--   sense in which the constructive order, though extensionally the classical one
--   (`lt_iff_toReal_lt`), is not a decidable relation on the approximating data.
--
--   ```lean
--   theorem Bishop.Reg.no_uniform_lt_witness(N : ℕ) :
--       ∃ x y : Reg, Lt x y ∧ ∀ n ≤ N, ¬ (x.approx n + 2 / (n + 1 : ℚ) < y.approx n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/ConstructiveOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/ConstructiveOrder.lean#L280

-- Thm stub generated from Logic/ConstructiveAnalysis/ConstructiveOrder.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveOrder
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


open Bishop

open Reg

/-! ## Two-sided form of the explicit modulus -/




/-! ## Positivity and the strict order -/














/-! ## Locating a Bishop real between two rationals -/




/-! ## The order is not decidable at bounded precision -/

theorem Bishop.Reg.no_uniform_lt_witness(N : ℕ) :
    ∃ x y : Reg, Lt x y ∧ ∀ n ≤ N, ¬ (x.approx n + 2 / (n + 1 : ℚ) < y.approx n) := by sorry
