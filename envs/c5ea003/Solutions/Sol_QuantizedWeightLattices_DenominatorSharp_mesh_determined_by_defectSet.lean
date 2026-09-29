-- Prove2me | solution 1 for QuantizedWeightLattices.DenominatorSharp.mesh_determined_by_defectSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:33:39.227611+00:00
-- url     : https://prove2.me/submissions/54781584-efd9-4259-af1b-650cebef3a50

-- Sol generated from Bridges/QuantizedWeightLatticesDenominatorSharp.lean
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLatticesDenominatorSharp
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant
import Theorems.Thm_QuantizedWeightLattices_DenominatorSharp_denominator_constant_exact
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


/-! ## Section 6: the denominator law for whole weight tensors -/


variable {ι : Type*} [Fintype ι] {L : NNReal} {f : (ι → ℝ) → ℝ}




/-! ## Section 7: a spectral converse — the defect set is an arithmetic fingerprint

The exact constants of Sections 4–5 can be read backwards: the convexity defects
of the quantized landscape are an *observable* of a training run (one measures the
violation of the convexity inequality), and they determine the arithmetic data of
the quantizer. -/




open QuantizedWeightLattices.DenominatorSharp in
theorem solution{δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') {k q : ℕ}
    (hq : 1 < q) (hk : k ≤ q) (hcop : Nat.Coprime k q)
    (h : defectSet δ k q = defectSet δ' k q) : δ = δ' := by
  have hq0 : 0 < q := lt_trans Nat.zero_lt_one hq
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h1 := denominator_constant_exact hδ hq0 hk hcop
  have h2 := denominator_constant_exact hδ' hq0 hk hcop
  rw [h] at h1
  have hmax : δ * (1 - 1 / (q : ℝ)) = δ' * (1 - 1 / (q : ℝ)) := h1.unique h2
  have hpos : 0 < 1 - 1 / (q : ℝ) := by
    have : 1 / (q : ℝ) < 1 := by
      rw [div_lt_one (by linarith)]
      exact hqR
    linarith
  exact mul_right_cancel₀ (ne_of_gt hpos) hmax
