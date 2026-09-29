-- Prove2me | Theorems.Thm_Catalog_NumberTheory_QuantMixedPrecision_bitCost_waterfilling
-- name    : Catalog.NumberTheory.QuantMixedPrecision.bitCost_waterfilling
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:24:37.564602+00:00
-- url     : https://prove2.me/theorems/c3f042cc-0b7a-40d1-b194-8f6e6634c315
-- title:
--   The water-filling allocation attains the bound.
-- statement:
--   **The water-filling allocation attains the bound.**
--
--   ```lean
--   theorem Catalog.NumberTheory.QuantMixedPrecision.bitCost_waterfilling{n : ℕ} (hn : 0 < n) {A : Fin n → ℝ} (hA : ∀ i, 0 < A i) (B : ℝ) :
--       bitCost A (waterfill A B)
--         = (n : ℝ) * ((∏ i, A i) ^ ((1:ℝ)/n) * (2:ℝ) ^ (-B / n)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/QuantMixedPrecision.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/QuantMixedPrecision.lean#L86

-- Thm stub generated from NumberTheory/QuantMixedPrecision.lean
import Mathlib
import Definitions.Def_NumberTheory_QuantMixedPrecision
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

open Catalog.NumberTheory.QuantMixedPrecision

open Finset

theorem Catalog.NumberTheory.QuantMixedPrecision.bitCost_waterfilling{n : ℕ} (hn : 0 < n) {A : Fin n → ℝ} (hA : ∀ i, 0 < A i) (B : ℝ) :
    bitCost A (waterfill A B)
      = (n : ℝ) * ((∏ i, A i) ^ ((1:ℝ)/n) * (2:ℝ) ^ (-B / n)) := by sorry
