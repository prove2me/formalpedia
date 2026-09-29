-- Prove2me | Theorems.Thm_QuantizedWeightLattices_DenominatorSharp_denominator_constant_reduced
-- name    : QuantizedWeightLattices.DenominatorSharp.denominator_constant_reduced
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:07:14.569957+00:00
-- url     : https://prove2.me/theorems/f9189a08-b861-4b44-bfc6-b7118441f02d
-- title:
--   Theorem S11 (only the reduced denominator matters).
-- statement:
--   **Theorem S11 (only the reduced denominator matters).**  For an arbitrary
--   mixing weight `k/q` with `0 < k < q`, the exact maximal convexity defect is
--   `(1 − g/q)·δ` where `g = gcd(k, q)`: the sharp constant depends on the *reduced*
--   denominator `q/g` alone.  Two mixing weights of the same value have the same
--   convexity cost, and a weight with a small reduced denominator (e.g. `1/2`) is
--   strictly gentler than a nearby weight with a large one.
--
--   ```lean
--   theorem QuantizedWeightLattices.DenominatorSharp.denominator_constant_reduced{δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hk0 : 0 < k) (hkq : k < q) :
--       IsGreatest (defectSet δ k q) (δ * (1 - (Nat.gcd k q : ℝ) / (q : ℝ))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/QuantizedWeightLatticesDenominatorSharp.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/QuantizedWeightLatticesDenominatorSharp.lean#L226

-- Thm stub generated from Bridges/QuantizedWeightLatticesDenominatorSharp.lean
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLatticesDenominatorSharp
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, VI:
# the denominator law is exact — the defect spectrum at a rational mixing weight

`Bridges.QuantizedWeightLatticesSharpConstant` proved the **denominator law**: for a
convex `L`-Lipschitz loss and the `δ`-grid quantizer, the convexity defect at the
interpolation weight `a = k/q` is at most `(1 − 1/q)·L·δ`, and it exhibited a
witness attaining the bound only for `k = q − 1`.  Conjecture 1 of
`FUTURE_DIRECTIONS.md` asked whether the bound is attained for *every* `k`
coprime to `q`.

This file settles that conjecture **affirmatively, and in a stronger form**:

* `defect_spectrum` — for `gcd(k, q) = 1` and *every* `j` with `0 ≤ j < q` there is
  an explicit convex `1`-Lipschitz loss (a "distance to a target weight" loss) and
  an explicit pair of weights whose quantized convexity defect at mixing weight
  `k/q` equals **exactly** `δ·j/q`.  The whole arithmetic progression
  `(δ/q)·{0, 1, …, q−1}` is realised: the defect spectrum is the full rank-one
  lattice slice predicted by the arithmetic half of the denominator law.
* `denominator_constant_exact` — consequently the supremum of the defect over all
  convex `1`-Lipschitz losses at mixing weight `k/q` is attained and equals
  `(1 − 1/q)·δ`; formally an `IsGreatest` statement, so the constant of the
  denominator law is optimal for every residue `k` coprime to `q`.
* `denominator_constant_reduced` — for a general (not necessarily reduced) weight
  `k/q` the sharp constant is `(1 − gcd(k,q)/q)·δ`, i.e. only the *reduced*
  denominator matters.  Arithmetic, not size, of the mixing weight controls the
  loss of convexity.
* `quantizeTensor_defect_denominator` — the denominator law itself lifts from `ℝ`
  to whole weight tensors `ι → ℝ` with the sup norm: entrywise `δ`-grid
  quantization of a transformer's weights loses at most `(1 − 1/q)·L·δ` of
  convexity at any mixing weight of denominator `q`.
* `mesh_determined_by_defectSet`, `reducedDenominator_determined_by_defectSet` — a
  spectral converse: the achievable convexity defects are an arithmetic
  fingerprint.  They determine the mesh `δ` of the quantizer and the *reduced*
  denominator of the mixing weight, both recoverable from landscape measurements
  alone.

The mechanism: all three roundings are lattice points, so the discrepancy
`a·Qx + (1−a)·Qy − Q(a x + (1−a) y)` lies in `(δ/q)·ℤ`; its numerator is
`k·(round X − round Y) mod q`, and as `round X − round Y` ranges over `ℤ` this
covers all of `ℤ/qℤ` exactly when `gcd(k, q) = 1`.  Attainment is therefore a
covering statement for the cyclic group `ℤ/qℤ`, and the covering witnesses are
produced here by Bézout.
-/


open QuantizedWeightLattices.DenominatorSharp

open Set QuantizedWeightLattices QuantizedWeightLattices.SharpConstant

/-! ## Section 1: the covering lemma for `ℤ/qℤ` -/


/-! ## Section 2: exact roundings of the witness points -/





/-! ## Section 3: the witness family realising an arbitrary lattice defect -/


/-! ## Section 4: the defect spectrum at a coprime mixing weight -/




/-! ## Section 5: general (non-reduced) mixing weights -/

theorem QuantizedWeightLattices.DenominatorSharp.denominator_constant_reduced{δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hk0 : 0 < k) (hkq : k < q) :
    IsGreatest (defectSet δ k q) (δ * (1 - (Nat.gcd k q : ℝ) / (q : ℝ))) := by sorry
