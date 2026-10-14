-- Prove2me | solution 1 for Hadamard.tensor_product_exists
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T04:06:07.322531+00:00
-- url     : https://prove2.me/submissions/ad0a0761-4dbe-4a23-a40a-e92a4282b9ea

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

open scoped Kronecker

theorem solution (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i j, A i j ∈ ({1, -1} : Finset ℝ))
    (hB : ∀ i j, B i j ∈ ({1, -1} : Finset ℝ))
    (hdA : |A.det| = (n : ℝ) ^ ((n : ℝ) / 2))
    (hdB : |B.det| = (m : ℝ) ^ ((m : ℝ) / 2)) :
    ∃ C : Matrix (Fin (n * m)) (Fin (n * m)) ℝ,
      (∀ i j, C i j ∈ ({1, -1} : Finset ℝ)) ∧
      |C.det| = ((n * m : ℕ) : ℝ) ^ (((n * m : ℕ) : ℝ) / 2) := by
  refine ⟨Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B), ?_, ?_⟩
  · intro i j
    change A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
      B (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 ∈ ({1, -1} : Finset ℝ)
    have ha := hA (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    have hb := hB (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> simp
  · rw [Matrix.det_reindex_self, Matrix.det_kronecker, abs_mul, abs_pow, abs_pow,
      Fintype.card_fin, Fintype.card_fin, hdA, hdB, Nat.cast_mul]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n),
      ← Real.rpow_mul_natCast (Nat.cast_nonneg m)]
    have hn : (n : ℝ) / 2 * m = (n : ℝ) * m / 2 := by ring
    have hm : (m : ℝ) / 2 * n = (n : ℝ) * m / 2 := by ring
    rw [hn, hm, Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg m)]
