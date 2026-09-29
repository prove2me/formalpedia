-- Prove2me | Definitions.Def_Bridges_QuantizedWeightLatticesDenominatorSharp
-- name    : Bridges_QuantizedWeightLatticesDenominatorSharp
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:36.772331+00:00
-- url     : https://prove2.me/theorems/9c850271-ad21-46c0-b234-a6865e1dfaa1
-- title:
--   Aether Catalog definitions — Bridges_QuantizedWeightLatticesDenominatorSharp
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.QuantizedWeightLatticesDenominatorSharp`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/QuantizedWeightLatticesDenominatorSharp.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
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


namespace QuantizedWeightLattices.DenominatorSharp

open Set QuantizedWeightLattices QuantizedWeightLattices.SharpConstant

/-! ## Section 1: the covering lemma for `ℤ/qℤ` -/


/-! ## Section 2: exact roundings of the witness points -/





/-! ## Section 3: the witness family realising an arbitrary lattice defect -/


/-! ## Section 4: the defect spectrum at a coprime mixing weight -/


/-- The set of convexity defects of `δ`-grid quantized landscapes of convex
`1`-Lipschitz losses, at the fixed mixing weight `a = k/q`. -/
def defectSet (δ : ℝ) (k q : ℕ) : Set ℝ :=
  {D : ℝ | ∃ (f : ℝ → ℝ) (x y : ℝ), ConvexOn ℝ univ f ∧ LipschitzWith 1 f ∧
    D = f (gridRound δ (((k : ℝ) / q) * x + (1 - (k : ℝ) / q) * y))
      - (((k : ℝ) / q) * f (gridRound δ x) + (1 - (k : ℝ) / q) * f (gridRound δ y))}


/-! ## Section 5: general (non-reduced) mixing weights -/


/-! ## Section 6: the denominator law for whole weight tensors -/

section Tensor

variable {ι : Type*} [Fintype ι] {L : NNReal} {f : (ι → ℝ) → ℝ}



end Tensor

/-! ## Section 7: a spectral converse — the defect set is an arithmetic fingerprint

The exact constants of Sections 4–5 can be read backwards: the convexity defects
of the quantized landscape are an *observable* of a training run (one measures the
violation of the convexity inequality), and they determine the arithmetic data of
the quantizer. -/



end QuantizedWeightLattices.DenominatorSharp


