-- Prove2me | Theorems.Thm_QuantizedWeightLattices_SharpConstant_quantized_approxConvexOn_of_approxConvexOn
-- name    : QuantizedWeightLattices.SharpConstant.quantized_approxConvexOn_of_approxConvexOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:08:34.882561+00:00
-- url     : https://prove2.me/theorems/59431739-59e5-4bdc-81e4-b761d3e3380d
-- title:
--   Quantization increases the defect by at most `2·L·r` (Theorem A with the
-- statement:
--   **Quantization increases the defect by at most `2·L·r`** (Theorem A with the
--   exact-convexity hypothesis relaxed to `ε`-approximate convexity).
--
--   ```lean
--   theorem QuantizedWeightLattices.SharpConstant.quantized_approxConvexOn_of_approxConvexOn(hL : LipschitzWith L f) (Q : Quantizer E)
--       {ε : ℝ} (h : ApproxConvexOn ε univ f) :
--       ApproxConvexOn (ε + 2 * (L : ℝ) * Q.radius) univ (f ∘ Q.toFun) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/QuantizedWeightLatticesSharpConstant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/QuantizedWeightLatticesSharpConstant.lean#L329

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

theorem QuantizedWeightLattices.SharpConstant.quantized_approxConvexOn_of_approxConvexOn(hL : LipschitzWith L f) (Q : Quantizer E)
    {ε : ℝ} (h : ApproxConvexOn ε univ f) :
    ApproxConvexOn (ε + 2 * (L : ℝ) * Q.radius) univ (f ∘ Q.toFun) := by sorry
