-- Prove2me | solution 1 for Catalog.NumberTheory.QuantMixedPrecision.bitCost_waterfilling
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-10T22:53:19.197058+00:00
-- url     : https://prove2.me/submissions/dc21b81f-33a0-44c6-af7c-5394d16499c9

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
theorem solution{n : ℕ} (hn : 0 < n) {A : Fin n → ℝ} (hA : ∀ i, 0 < A i) (B : ℝ) :
    bitCost A (waterfill A B)
      = (n : ℝ) * ((∏ i, A i) ^ ((1:ℝ)/n) * (2:ℝ) ^ (-B / n)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ i, A i * (2:ℝ) ^ (-(waterfill A B i))
      = (∏ j, A j) ^ ((1:ℝ)/n) * (2:ℝ) ^ (-B / n) := by
    intro i
    have hsplit : -(waterfill A B i)
        = -B / n - Real.logb 2 (A i) + (∑ j, Real.logb 2 (A j)) / n := by
      rw [waterfill]; ring
    rw [hsplit, Real.rpow_add (by norm_num), Real.rpow_sub (by norm_num)]
    have hAi : (2:ℝ) ^ (Real.logb 2 (A i)) = A i :=
      Real.rpow_logb (by norm_num) (by norm_num) (hA i)
    have hsumlog : (2:ℝ) ^ ((∑ j, Real.logb 2 (A j)) / n) = (∏ j, A j) ^ ((1:ℝ)/n) := by
      have h1 : (2:ℝ) ^ (∑ j, Real.logb 2 (A j)) = ∏ j, A j := by
        rw [Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)]
        exact Finset.prod_congr rfl fun j _ =>
          Real.rpow_logb (by norm_num) (by norm_num) (hA j)
      calc (2:ℝ) ^ ((∑ j, Real.logb 2 (A j)) / n)
          = ((2:ℝ) ^ (∑ j, Real.logb 2 (A j))) ^ ((1:ℝ)/n) := by
            rw [← Real.rpow_mul (by norm_num)]
            congr 1
            field_simp
        _ = (∏ j, A j) ^ ((1:ℝ)/n) := by rw [h1]
    have hAi0 : A i ≠ 0 := (hA i).ne'
    rw [hAi, hsumlog]
    field_simp
  rw [bitCost, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
