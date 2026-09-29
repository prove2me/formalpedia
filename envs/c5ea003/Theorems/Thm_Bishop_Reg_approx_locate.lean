-- Prove2me | Theorems.Thm_Bishop_Reg_approx_locate
-- name    : Bishop.Reg.approx_locate
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:17:32.627674+00:00
-- url     : https://prove2.me/theorems/271348c9-1377-41b9-9716-eb86c146ecd8
-- title:
--   Constructive location.
-- statement:
--   **Constructive location.**  For rationals `a < b` and any Bishop real `x`, a
--   single rational comparison at a computed index decides `a < x` or `x < b`.  (The
--   classically trivial `a < x ∨ x ≤ a` is *not* constructively available; this
--   overlapping disjunction is its constructive replacement.)
--
--   ```lean
--   theorem Bishop.Reg.approx_locate(x : Reg) {a b : ℚ} (hab : a < b) :
--       (a : ℝ) < x.toReal ∨ x.toReal < (b : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/ConstructiveOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/ConstructiveOrder.lean#L259

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

theorem Bishop.Reg.approx_locate(x : Reg) {a b : ℚ} (hab : a < b) :
    (a : ℝ) < x.toReal ∨ x.toReal < (b : ℝ) := by sorry
