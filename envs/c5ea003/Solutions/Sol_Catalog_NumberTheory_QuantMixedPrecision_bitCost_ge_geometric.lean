-- Prove2me | solution 1 for Catalog.NumberTheory.QuantMixedPrecision.bitCost_ge_geometric
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-10T22:53:18.622658+00:00
-- url     : https://prove2.me/submissions/408b9bdc-000e-4023-bb24-49656ae14e2f

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
theorem solution{n : ℕ} (hn : 0 < n) {A b : Fin n → ℝ} (hA : ∀ i, 0 < A i) :
    (n : ℝ) * ((∏ i, A i) ^ ((1:ℝ)/n) * (2:ℝ) ^ (-(∑ i, b i) / n)) ≤ bitCost A b := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  set z : Fin n → ℝ := fun i => A i * (2:ℝ) ^ (-(b i)) with hz
  have hzpos : ∀ i, 0 < z i := fun i => mul_pos (hA i) (Real.rpow_pos_of_pos (by norm_num) _)
  have hw : ∑ _i : Fin n, (1:ℝ)/n = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1:ℝ)/n) z
    (fun i _ => by positivity) hw (fun i _ => (hzpos i).le)
  have hprodz : ∏ i, z i = (∏ i, A i) * (2:ℝ) ^ (-(∑ i, b i)) := by
    have h1 : (2:ℝ) ^ (-(∑ i, b i)) = ∏ i, (2:ℝ) ^ (-(b i)) := by
      rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)]
      congr 1
      simp
    rw [hz, Finset.prod_mul_distrib, h1]
  have hgeom : ∏ i, z i ^ ((1:ℝ)/n)
      = (∏ i, A i) ^ ((1:ℝ)/n) * (2:ℝ) ^ (-(∑ i, b i) / n) := by
    rw [Real.finset_prod_rpow _ _ (fun i _ => (hzpos i).le), hprodz,
      Real.mul_rpow (Finset.prod_nonneg fun i _ => (hA i).le)
        (Real.rpow_nonneg (by norm_num) _)]
    congr 1
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    field_simp
  rw [hgeom] at hamgm
  have hsum : ∑ i, (1:ℝ)/n * z i = bitCost A b / n := by
    rw [bitCost, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz]
    field_simp
  rw [hsum] at hamgm
  have hcancel : (n:ℝ) * (bitCost A b / n) = bitCost A b := by field_simp
  have hmul := mul_le_mul_of_nonneg_left hamgm hnR.le
  linarith [hcancel, hmul]
