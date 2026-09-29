-- Prove2me | solution 1 for Catalog.NumberTheory.QuantMixedPrecision.uniform_not_optimal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-10T22:53:19.819798+00:00
-- url     : https://prove2.me/submissions/3856f74f-e8b0-491f-9195-9938e766364e

-- Sol generated from NumberTheory/QuantMixedPrecision.lean
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








open Catalog.NumberTheory.QuantMixedPrecision in
theorem solution:
    ∃ A b : Fin 2 → ℝ, (∀ i, 0 < A i) ∧ ∑ i, b i = 0 ∧
      bitCost A b < bitCost A (fun _ => 0) := by
  refine ⟨![1, 4], ![-1, 1], ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · simp [Fin.sum_univ_two]
  · have h1 : (2:ℝ) ^ (-(-1 : ℝ)) = 2 := by
      rw [neg_neg, Real.rpow_one]
    have h2 : (2:ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
      rw [Real.rpow_neg_one]
      norm_num
    have h3 : (2:ℝ) ^ (-(0 : ℝ)) = 1 := by
      rw [neg_zero, Real.rpow_zero]
    simp only [bitCost, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      h1, h2, h3]
    norm_num
