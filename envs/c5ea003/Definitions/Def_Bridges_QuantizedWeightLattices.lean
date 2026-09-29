-- Prove2me | Definitions.Def_Bridges_QuantizedWeightLattices
-- name    : Bridges_QuantizedWeightLattices
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:33:52.382279+00:00
-- url     : https://prove2.me/theorems/c1dca385-0bf0-4fed-a4dc-652e71d09bf8
-- title:
--   Aether Catalog definitions — Bridges_QuantizedWeightLattices
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.QuantizedWeightLattices`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/QuantizedWeightLattices.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, I: the analytic core

Quantizing a transformer's weight tensor means replacing each real entry by the
nearest point of a *modular lattice grid* `δ·ℤ ⊆ ℝ` (in practice: an integer
`INT-k` code times a scale).  This file proves that this operation preserves the
**global convexity invariants** of the loss landscape *quantitatively*:

* the quantized loss `f ∘ Q` is `2Lr`-approximately convex (`quantized_approxConvex`);
* the best lattice weight is within `L·r` of the *global* optimum
  (`quantized_min_gap`), where `r` is the covering radius of the grid;
* under quadratic growth the lattice minimiser is `√(2Lr/μ)`-close to the true
  minimiser (`quantized_minimizer_close`);
* sublevel sets of the quantized loss are sandwiched between two genuinely convex
  sets (`sublevel_sandwich`), so all sublevel-convexity invariants survive up to
  the covering radius;
* **capstone / reverse transfer**: if along a tower of refining lattices the
  quantized landscapes are `εₘ`-approximately convex with `εₘ → 0`, then the
  underlying continuous loss is *exactly* convex (`convexOn_of_approxConvex_tower`).
  Convexity is therefore an invariant certifiable from finite, quantized data.

The arithmetic (modular / CRT / lattice-tower) layer lives in
`Bridges.QuantizedWeightLatticesModular`.
-/


namespace QuantizedWeightLattices

open Set Filter Topology

/-! ## Section 1: the scalar grid quantizer `δ·ℤ` -/

/-- Rounding a real number to the nearest point of the lattice `δ·ℤ`. -/
noncomputable def gridRound (δ x : ℝ) : ℝ := δ * (round (x / δ) : ℤ)


/-- **Covering radius of the grid**: rounding moves a weight by at most `δ/2`. -/
lemma gridRound_error {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : |gridRound δ x - x| ≤ δ / 2 := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hx : gridRound δ x - x = δ * ((round (x / δ) : ℝ) - x / δ) := by
    simp only [gridRound]; field_simp
  have h2 : |(round (x / δ) : ℝ) - x / δ| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round (x / δ)
  rw [hx, abs_mul, abs_of_pos hδ]
  nlinarith [abs_nonneg ((round (x / δ) : ℝ) - x / δ)]



/-! ## Section 2: quantizing a whole weight tensor

A transformer weight tensor is a function `ι → ℝ` for a finite index type `ι`
(e.g. `ι = Fin dout × Fin din` for one matrix, or a sigma type over all layers).
`ι → ℝ` carries the sup norm, the natural norm for entrywise quantization. -/

section Tensor

variable {ι : Type*} [Fintype ι]

/-- Entrywise quantization of a weight tensor onto the lattice `(δ·ℤ)^ι`. -/
noncomputable def quantizeTensor (δ : ℝ) (W : ι → ℝ) : ι → ℝ := fun i => gridRound δ (W i)


/-- **Uniform quantization error**: the tensor moves by at most `δ/2` in sup norm. -/
lemma quantizeTensor_error {δ : ℝ} (hδ : 0 < δ) (W : ι → ℝ) :
    ‖quantizeTensor δ W - W‖ ≤ δ / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simpa [quantizeTensor, Real.norm_eq_abs] using gridRound_error hδ (W i)


end Tensor

/-! ## Section 3: abstract quantizers -/

/-- A `Quantizer` on a normed space is any map whose displacement is uniformly
bounded by its `radius` (the covering radius of the target lattice).  Nearest-point
projection to a full-rank lattice is the motivating example. -/
structure Quantizer (E : Type*) [SeminormedAddCommGroup E] where
  /-- the quantization map -/
  toFun : E → E
  /-- covering radius of the target lattice -/
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  error_le : ∀ x, ‖toFun x - x‖ ≤ radius

/-- The entrywise grid quantizer as a `Quantizer` with covering radius `δ/2`. -/
noncomputable def gridQuantizer {ι : Type*} [Fintype ι] {δ : ℝ} (hδ : 0 < δ) :
    Quantizer (ι → ℝ) where
  toFun := quantizeTensor δ
  radius := δ / 2
  radius_nonneg := by positivity
  error_le := quantizeTensor_error hδ

/-! ## Section 4: approximate convexity -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `ApproxConvexOn ε s g`: convexity up to an additive defect `ε`. -/
def ApproxConvexOn (ε : ℝ) (s : Set E) (g : E → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    g (a • x + b • y) ≤ a * g x + b * g y + ε




/-! ## Section 5: transfer of convexity through quantization -/

section Transfer

variable {L : NNReal} {f : E → ℝ}








end Transfer

/-! ## Section 6: the capstone — exact convexity from the lattice tower -/


/-! ## Section 7: the concrete grid tower -/

section GridTower

variable {ι : Type*} [Fintype ι]



/-- The tower of grid quantizers on a weight tensor space, `Qₘ` with mesh `δ/(m+1)`. -/
noncomputable def gridTower (δ : ℝ) (hδ : 0 < δ) (m : ℕ) : Quantizer (ι → ℝ) :=
  gridQuantizer (ι := ι) (δ := δ / (m + 1)) (by positivity)




end GridTower

end QuantizedWeightLattices


