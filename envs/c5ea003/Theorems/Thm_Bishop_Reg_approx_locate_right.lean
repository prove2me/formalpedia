-- Prove2me | Theorems.Thm_Bishop_Reg_approx_locate_right
-- name    : Bishop.Reg.approx_locate_right
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:17:22.750591+00:00
-- url     : https://prove2.me/theorems/9e72da18-0397-4939-8520-1533fdb16e0e
-- title:
--   If the `n`-th approximation is below the midpoint of `[a,b]`, and the index is
-- statement:
--   If the `n`-th approximation is below the midpoint of `[a,b]`, and the index is
--   fine enough, then the real denoted by `x` is strictly below `b`.
--
--   ```lean
--   theorem Bishop.Reg.approx_locate_right{x : Reg} {a b : ℚ} {n : ℕ}
--       (hn : 4 / (n + 1 : ℚ) ≤ b - a) (h : x.approx n < (a + b) / 2) :
--       x.toReal < (b : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/ConstructiveOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/ConstructiveOrder.lean#L236

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

theorem Bishop.Reg.approx_locate_right{x : Reg} {a b : ℚ} {n : ℕ}
    (hn : 4 / (n + 1 : ℚ) ≤ b - a) (h : x.approx n < (a + b) / 2) :
    x.toReal < (b : ℝ) := by sorry
