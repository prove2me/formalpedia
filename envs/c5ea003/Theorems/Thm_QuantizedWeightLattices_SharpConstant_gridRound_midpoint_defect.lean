-- Prove2me | Theorems.Thm_QuantizedWeightLattices_SharpConstant_gridRound_midpoint_defect
-- name    : QuantizedWeightLattices.SharpConstant.gridRound_midpoint_defect
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:08:16.355554+00:00
-- url     : https://prove2.me/theorems/5c135b0d-73c0-4c1e-b9e4-5abc85aaca51
-- title:
--   The scalar case of `quantizeTensor_midpoint_defect`, stated directly for
-- statement:
--   The scalar case of `quantizeTensor_midpoint_defect`, stated directly for
--   `gridRound` on `ℝ`.
--
--   ```lean
--   theorem QuantizedWeightLattices.SharpConstant.gridRound_midpoint_defect{L : NNReal} {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
--       (hL : LipschitzWith L f) {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
--       f (gridRound δ ((x + y) / 2))
--         ≤ (1 / 2 : ℝ) * f (gridRound δ x) + (1 / 2 : ℝ) * f (gridRound δ y)
--           + (L : ℝ) * (δ / 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/QuantizedWeightLatticesSharpConstant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/QuantizedWeightLatticesSharpConstant.lean#L150

-- Thm stub generated from Bridges/QuantizedWeightLatticesSharpConstant.lean
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
import Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, V:
# the exact convexity defect of nearest-point grid quantization

This file closes the first open conjecture of `FUTURE_DIRECTIONS.md`
("the sharp constant is `L·r`, not `2·L·r`, for *nearest-point* quantizers").

The conjecture is **false**, and it is refuted here by an explicit convex
`1`-Lipschitz loss:

* `targetLoss_defect_ge` — the "distance to the target weight" loss
  `f w = |w − δ|` composed with `δ`-grid rounding has convexity defect
  `≥ (1 − 1/n)·δ` for every `n ≥ 3`, hence
* `gridRound_defect_ge` — defect `≥ δ = 2·L·r`.  Combined with Theorem A
  (`quantized_approxConvex`) the sharp constant for the nearest-point grid
  quantizer is **exactly** `2·L·r` (`grid_defect_constant_exact`), and the
  conjectured `L·r` bound fails (`grid_defect_Lr_refuted`).

The earlier computational scans missed this because they only tested losses
(`|x|`, `x²`, a two-kink loss) that are *symmetric around a grid point*; the
extremal configuration needs a strongly unbalanced convex combination `a → 1`
together with a loss that decreases across the offending grid cell.

The failure is however confined to unbalanced combinations.  The second half of
the file proves the complementary **positive** result:

* `two_round_midpoint_sub_le` — the arithmetic heart, an integer parity
  statement: `|round X + round Y − 2·round((X+Y)/2)| ≤ 1`;
* `gridRound_midpoint_dist` — hence rounding the midpoint of two weights differs
  from the midpoint of the two rounded weights by at most `δ/2`;
* `quantizeTensor_midpoint_defect` — hence for *weight averaging* (`a = b = ½`,
  the "model soup" regime) the entrywise-quantized landscape of a convex
  `L`-Lipschitz loss has defect at most `L·δ/2 = L·r`, **half** the general
  bound, and that constant is sharp (`midpoint_constant_sharp`).

So the true picture is: defect `= 2·L·r` in general, `= L·r` on balanced
combinations.
-/

open QuantizedWeightLattices.SharpConstant

open QuantizedWeightLattices QuantizedWeightLattices.Sharp Set

/-! ## Section 1: an integer parity lemma for nearest-point rounding -/



/-! ## Section 2: the midpoint (weight-averaging) defect is only `L·r` -/


variable {ι : Type*} [Fintype ι]


variable {L : NNReal} {f : (ι → ℝ) → ℝ}

theorem QuantizedWeightLattices.SharpConstant.gridRound_midpoint_defect{L : NNReal} {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hL : LipschitzWith L f) {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    f (gridRound δ ((x + y) / 2))
      ≤ (1 / 2 : ℝ) * f (gridRound δ x) + (1 / 2 : ℝ) * f (gridRound δ y)
        + (L : ℝ) * (δ / 2) := by sorry
