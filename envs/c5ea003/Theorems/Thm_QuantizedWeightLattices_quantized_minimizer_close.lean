-- Prove2me | Theorems.Thm_QuantizedWeightLattices_quantized_minimizer_close
-- name    : QuantizedWeightLattices.quantized_minimizer_close
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:08:57.053733+00:00
-- url     : https://prove2.me/theorems/98c88b21-c421-4444-9d28-531a592b51a5
-- title:
--   Theorem C (minimiser localisation).
-- statement:
--   **Theorem C (minimiser localisation).**  If the loss has quadratic growth of
--   modulus `μ > 0` around its minimiser `x₀` (the standard consequence of strong
--   convexity) then *any* loss-minimising lattice point `ŵ` lies within
--   `√(2Lr/μ)` of `x₀`: quantization cannot relocate the basin of attraction.
--
--   ```lean
--   theorem QuantizedWeightLattices.quantized_minimizer_close{μ : ℝ} (hμ : 0 < μ) {x₀ ŵ : E}
--       (hL : LipschitzWith L f) (Q : Quantizer E)
--       (hgrowth : ∀ x, μ / 2 * ‖x - x₀‖ ^ 2 ≤ f x - f x₀)
--       (hlat : ∀ x, f ŵ ≤ f (Q.toFun x)) :
--       ‖ŵ - x₀‖ ≤ Real.sqrt (2 * (L : ℝ) * Q.radius / μ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/QuantizedWeightLattices.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/QuantizedWeightLattices.lean#L211

-- Thm stub generated from Bridges/QuantizedWeightLattices.lean
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
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


open QuantizedWeightLattices

open Set Filter Topology

/-! ## Section 1: the scalar grid quantizer `δ·ℤ` -/






/-! ## Section 2: quantizing a whole weight tensor

A transformer weight tensor is a function `ι → ℝ` for a finite index type `ι`
(e.g. `ι = Fin dout × Fin din` for one matrix, or a sigma type over all layers).
`ι → ℝ` carries the sup norm, the natural norm for entrywise quantization. -/


variable {ι : Type*} [Fintype ι]






/-! ## Section 3: abstract quantizers -/



/-! ## Section 4: approximate convexity -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





/-! ## Section 5: transfer of convexity through quantization -/


variable {L : NNReal} {f : E → ℝ}






omit [NormedSpace ℝ E] in

theorem QuantizedWeightLattices.quantized_minimizer_close{μ : ℝ} (hμ : 0 < μ) {x₀ ŵ : E}
    (hL : LipschitzWith L f) (Q : Quantizer E)
    (hgrowth : ∀ x, μ / 2 * ‖x - x₀‖ ^ 2 ≤ f x - f x₀)
    (hlat : ∀ x, f ŵ ≤ f (Q.toFun x)) :
    ‖ŵ - x₀‖ ≤ Real.sqrt (2 * (L : ℝ) * Q.radius / μ) := by sorry
