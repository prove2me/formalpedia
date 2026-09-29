-- Prove2me | solution 1 for block_diagonal_quadratic_form_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-25T02:33:22.575245+00:00
-- url     : https://prove2.me/submissions/37a0d883-a462-4c42-829d-2af3783b1517

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic
import Mathlib.Order.CompleteLattice.Finset

open Matrix
open scoped BigOperators

theorem solution {n1 n2 : ℕ}
    (a : Fin n1 → ℝ) (b : Fin n2 → ℝ) (B : ℝ)
    (ha : ∀ i, a i ≤ B) (hb : ∀ j, b j ≤ B)
    (ha0 : ∀ i, (0:ℝ) ≤ a i) (hb0 : ∀ j, (0:ℝ) ≤ b j)
    (w : Fin n1 ⊕ Fin n2 → ℝ) :
    (star w ⬝ᵥ (Matrix.fromBlocks (diagonal a) 0 0 (diagonal b)) *ᵥ w)
      ≤ B * (star w ⬝ᵥ w) := by
  classical
  -- diagonal quadratic-form bound (inlined helper)
  have diagonal_quadratic_form_le : ∀ {m : ℕ} (dd : Fin m → ℝ) (hdd : ∀ k, dd k ≤ B)
      (hdd0 : ∀ k, (0:ℝ) ≤ dd k) (u : Fin m → ℝ),
      (star u ⬝ᵥ (diagonal dd) *ᵥ u) ≤ B * (star u ⬝ᵥ u) := by
    intro m dd hdd hdd0 u
    have hL : (star u ⬝ᵥ (diagonal dd) *ᵥ u) = ∑ k, dd k * (u k * u k) := by
      rw [dotProduct]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [mulVec_diagonal]
      simp [Pi.star_apply, star_trivial]; ring
    have hR : B * (star u ⬝ᵥ u) = ∑ k, B * (u k * u k) := by
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [Pi.star_apply, star_trivial]
    rw [hL, hR]
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact mul_le_mul_of_nonneg_right (hdd k) (mul_self_nonneg _)
  set v1 : Fin n1 → ℝ := fun i => w (Sum.inl i) with hv1
  set v2 : Fin n2 → ℝ := fun j => w (Sum.inr j) with hv2
  have hmv : (Matrix.fromBlocks (diagonal a) 0 0 (diagonal b)) *ᵥ w
      = Sum.elim ((diagonal a) *ᵥ v1) ((diagonal b) *ᵥ v2) := by
    rw [fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, zero_add]
    rfl
  rw [hmv]
  have hsplit : (star w ⬝ᵥ Sum.elim ((diagonal a) *ᵥ v1) ((diagonal b) *ᵥ v2))
      = (star v1 ⬝ᵥ (diagonal a) *ᵥ v1) + (star v2 ⬝ᵥ (diagonal b) *ᵥ v2) := by
    rw [dotProduct, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.star_apply, hv1, hv2]
    rfl
  have hww : (star w ⬝ᵥ w) = (star v1 ⬝ᵥ v1) + (star v2 ⬝ᵥ v2) := by
    rw [dotProduct, Fintype.sum_sum_type]
    simp only [Pi.star_apply, hv1, hv2]
    rfl
  rw [hsplit, hww, mul_add]
  have h1 := diagonal_quadratic_form_le a ha ha0 v1
  have h2 := diagonal_quadratic_form_le b hb hb0 v2
  linarith
