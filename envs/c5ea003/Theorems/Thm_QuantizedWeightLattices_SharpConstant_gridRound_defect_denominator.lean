-- Prove2me | Theorems.Thm_QuantizedWeightLattices_SharpConstant_gridRound_defect_denominator
-- name    : QuantizedWeightLattices.SharpConstant.gridRound_defect_denominator
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:06:22.887631+00:00
-- url     : https://prove2.me/theorems/d4eb72b5-a0ab-4806-85c1-d8f092c0fc42
-- title:
--   The denominator law.
-- statement:
--   **The denominator law.**  For a convex `L`-Lipschitz loss, the `δ`-grid
--   quantized landscape satisfies the convexity inequality at every interpolation
--   weight `a = k/q` with defect at most `(1 − 1/q)·L·δ = (1 − 1/q)·2·L·r`.
--
--   Balanced weights (`q = 2`) lose only `L·r`; the general bound `2·L·r` is
--   approached only along weights of large denominator.
--
--   ```lean
--   theorem QuantizedWeightLattices.SharpConstant.gridRound_defect_denominator{L : NNReal} {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
--       (hL : LipschitzWith L f) {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hq : 0 < q) (hk : k ≤ q) (x y : ℝ) :
--       f (gridRound δ ((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y))
--         ≤ (k / q : ℝ) * f (gridRound δ x) + (1 - (k / q : ℝ)) * f (gridRound δ y)
--           + (L : ℝ) * (δ * (1 - 1 / q)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/QuantizedWeightLatticesSharpConstant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/QuantizedWeightLatticesSharpConstant.lean#L535

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





/-! ## Section 3: refutation of the `L·r` conjecture for unbalanced combinations

The loss is `f w = |w − δ|`, the distance to the target weight `δ` (itself a grid
point); it is convex and `1`-Lipschitz.  The two sample weights are `δ/2` and
`−δ/2`, which round *away from each other* to `δ` and `0`; their convex
combination with weights `a = 1 − 1/n` and `b = 1/n` sits just below the rounding
threshold `δ/2` and therefore rounds *down* to `0`, where the loss is maximal. -/










/-! ## Section 4: the finite-precision convexity audit

Theorem E of `QuantizedWeightLattices.lean` recovers *exact* convexity of the
continuous loss from an infinite tower of quantized landscapes with vanishing
defects.  The following two statements are its *finite* counterpart, and they
resolve the analytic half of Conjecture 5 of `FUTURE_DIRECTIONS.md`: a single
precision already certifies convexity of the continuous loss up to `2·L·r`, and
the correspondence is two-sided — quantization changes the convexity defect of an
`L`-Lipschitz landscape by at most `2·L·r`, in either direction. -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : NNReal} {f : E → ℝ}






/-! ## Section 5: the denominator law

The two extreme cases proved above — defect `L·r` for the balanced weight `a = 1/2`
and defect `→ 2·L·r` along `a = 1 − 1/n` — are the first instances of a single
**arithmetic law**: the sharp convexity defect at an interpolation weight
`a = k/q` (in lowest terms) is governed by the *denominator* `q`,

  `defect ≤ (1 − 1/q) · L · δ = (1 − 1/q) · 2·L·r`.

The reason is purely number-theoretic: the discrepancy
`A = a·Qx + (1−a)·Qy − Q(a x + (1−a) y)` is a multiple of `δ/q` (all three
roundings are lattice points and `a` has denominator `q`), while three
covering-radius estimates force `|A| < δ`; an integer strictly smaller than `q` is
at most `q − 1`.  The convex-analytic half converts `|A|` into a defect bound.

For `q = 2` this returns `L·δ/2 = L·r`, and the bound is attained for every `q`
at `a = (q−1)/q` (`targetLoss_defect_eq`), so the law is sharp along that family. -/

theorem QuantizedWeightLattices.SharpConstant.gridRound_defect_denominator{L : NNReal} {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hL : LipschitzWith L f) {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hq : 0 < q) (hk : k ≤ q) (x y : ℝ) :
    f (gridRound δ ((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y))
      ≤ (k / q : ℝ) * f (gridRound δ x) + (1 - (k / q : ℝ)) * f (gridRound δ y)
        + (L : ℝ) * (δ * (1 - 1 / q)) := by sorry
