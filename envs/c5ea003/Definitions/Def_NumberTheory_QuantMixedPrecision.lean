-- Prove2me | Definitions.Def_NumberTheory_QuantMixedPrecision
-- name    : NumberTheory_QuantMixedPrecision
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:16.892755+00:00
-- url     : https://prove2.me/theorems/ea07d4ab-71c5-4275-9f4b-39e4557684c3
-- title:
--   Aether Catalog definitions — NumberTheory_QuantMixedPrecision
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.QuantMixedPrecision`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/QuantMixedPrecision.lean by skeleton subtraction
import Mathlib
/-
# Optimal mixed precision: the water-filling law for bit allocation

The NET-52 round closes with the question of *tail-aware mixed precision*: given a fixed total
bit budget spread over tensors of differing amplitude, how should the bits be allocated?

For absmax round-to-nearest, the worst-case `ℓ¹` damage of tensor `i` is proportional to its
amplitude `A i` times `2 ^ (−b i)`, so the natural objective is

`bitCost A b = ∑ i, A i · 2 ^ (−b i)`,  subject to  `∑ i, b i = B`.

We prove the exact optimum:

* `bitCost_ge_geometric` — for *every* allocation with total budget `B`,
  `bitCost A b ≥ n · (∏ A i)^(1/n) · 2 ^ (−B/n)`.  The bound is the arithmetic–geometric mean
  inequality applied to the per-tensor damages, so the geometric mean of the amplitudes — not
  their maximum or their sum — is the invariant that governs a memory budget.
* `bitCost_waterfilling` — the explicit allocation `b i = B/n + log₂ (A i) − mean log₂ A`
  spends exactly `B` bits and *attains* the bound: the optimum is achieved by giving each
  tensor a number of extra bits equal to its log-amplitude excess.
* `uniform_not_optimal` — a concrete two-tensor witness (`A = (1,4)`, `B = 0`) where the
  optimal allocation costs `4` and the uniform allocation costs `5`: uniform precision is
  strictly suboptimal as soon as amplitudes are unequal, which is the formal reason the
  measured group-wise and depth-split arms differ.
-/

namespace Catalog.NumberTheory.QuantMixedPrecision

open Finset

/-- Worst-case damage proxy of a mixed-precision allocation `b` for tensor amplitudes `A`. -/
noncomputable def bitCost {n : ℕ} (A b : Fin n → ℝ) : ℝ := ∑ i, A i * (2:ℝ) ^ (-(b i))


/-- The water-filling allocation: base budget plus log-amplitude excess. -/
noncomputable def waterfill {n : ℕ} (A : Fin n → ℝ) (B : ℝ) : Fin n → ℝ :=
  fun i => B / n + Real.logb 2 (A i) - (∑ j, Real.logb 2 (A j)) / n




end Catalog.NumberTheory.QuantMixedPrecision


