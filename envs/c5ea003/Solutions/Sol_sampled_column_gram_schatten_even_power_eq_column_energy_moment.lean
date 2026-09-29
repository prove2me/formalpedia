-- Prove2me | solution 1 for sampled_column_gram_schatten_even_power_eq_column_energy_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T01:58:53.467695+00:00
-- url     : https://prove2.me/submissions/f6bd827f-ee50-4742-b4c0-5bb52357cb10

import Definitions.Def_matrix_completion_gram_schatten
import Mathlib.Tactic

open MatrixCompletion
open scoped BigOperators

private lemma column_energy_nonneg {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) (j : Fin n2) :
    0 ≤ ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0 := by
  classical
  apply Finset.sum_nonneg
  intro i _
  by_cases h : (i, j) ∈ Omega
  · simp [h, sq_nonneg]
  · simp [h]

private lemma column_gram_summand_even
    {n1 n2 : Nat} (n : Nat) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (X : RealMatrix n1 n2) (j : Fin n2) :
    Real.rpow
        (p⁻¹ * Real.sqrt (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0))
        (2 * n : ℝ)
      =
    (p⁻¹ ^ 2 *
      (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n := by
  classical
  let E : ℝ := ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0
  have hE : 0 ≤ E := by
    dsimp [E]
    exact column_energy_nonneg Omega X j
  change Real.rpow (p⁻¹ * Real.sqrt E) (2 * (n : ℝ)) = (p⁻¹ ^ 2 * E) ^ n
  have hcast : 2 * (n : ℝ) = ((2 * n : Nat) : ℝ) := by norm_num
  rw [hcast]
  have hnat :
      Real.rpow (p⁻¹ * Real.sqrt E) ((2 * n : Nat) : ℝ)
        = (p⁻¹ * Real.sqrt E) ^ (2 * n) := by
    simpa using Real.rpow_natCast (p⁻¹ * Real.sqrt E) (2 * n)
  rw [hnat]
  calc
    (p⁻¹ * Real.sqrt E) ^ (2 * n)
        = ((p⁻¹ * Real.sqrt E) ^ 2) ^ n := by
          rw [← pow_mul]
    _ = (p⁻¹ ^ 2 * E) ^ n := by
          congr 1
          rw [mul_pow, Real.sq_sqrt hE]

theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    (sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)
      =
    ∑ j : Fin n2,
      (p⁻¹ ^ 2 *
        (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n := by
  classical
  unfold sampledColumnGramSchatten
  let A : ℝ :=
    ∑ j : Fin n2,
      Real.rpow
        (p⁻¹ * Real.sqrt
          (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0))
        (2 * n : ℝ)
  have hsum_nonneg :
      0 ≤ A := by
    dsimp [A]
    apply Finset.sum_nonneg
    intro j _
    apply Real.rpow_nonneg
    exact mul_nonneg (inv_nonneg.mpr hp.le) (Real.sqrt_nonneg _)
  change Real.rpow A ((2 * (n : ℝ))⁻¹) ^ (2 * n) =
    ∑ j : Fin n2,
      (p⁻¹ ^ 2 *
        (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n
  have hcast : 2 * (n : ℝ) = ((2 * n : Nat) : ℝ) := by norm_num
  rw [hcast]
  have hcollapse :
      Real.rpow A (((2 * n : Nat) : ℝ)⁻¹) ^ (2 * n) = A := by
    simpa using
      (Real.rpow_inv_natCast_pow (x := A) hsum_nonneg (by omega : 2 * n ≠ 0))
  rw [hcollapse]
  dsimp [A]
  apply Finset.sum_congr rfl
  intro j _
  exact column_gram_summand_even n Omega p X j
