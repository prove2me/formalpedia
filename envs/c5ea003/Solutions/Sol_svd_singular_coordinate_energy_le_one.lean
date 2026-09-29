-- Prove2me | solution 1 for svd_singular_coordinate_energy_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T17:11:39.476618+00:00
-- url     : https://prove2.me/submissions/9e2793f7-ca84-4328-aa10-541f6704b9fb

import Mathlib.Tactic
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

open scoped Classical BigOperators

private lemma coordinate_energy_le_one_of_orthonormal
    {N r : ℕ} (u : Fin r → Fin N → ℝ)
    (horth : ∀ k l : Fin r,
      ∑ i : Fin N, u k i * u l i = if k = l then 1 else 0) :
    ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ (1 : ℝ) := by
  intro i
  let P : Fin N → ℝ := fun a => ∑ k : Fin r, u k i * u k a
  have hP_nonneg : 0 ≤ P i := by
    dsimp [P]
    exact Finset.sum_nonneg fun k _ => by nlinarith [sq_nonneg (u k i)]
  have hsum_idem : ∑ a : Fin N, (P a) ^ 2 = P i := by
    calc
      ∑ a : Fin N, (P a) ^ 2
          = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r,
              (u k i * u l i) * (u k a * u l a) := by
            dsimp [P]
            apply Finset.sum_congr rfl
            intro a _ha
            simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            apply Finset.sum_congr rfl
            intro l _hl
            ring
      _ = ∑ k : Fin r, ∑ l : Fin r,
            (u k i * u l i) * (∑ a : Fin N, u k a * u l a) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _hk
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro l _hl
            rw [Finset.mul_sum]
      _ = ∑ k : Fin r, ∑ l : Fin r,
            (u k i * u l i) * (if k = l then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro k _hk
            apply Finset.sum_congr rfl
            intro l _hl
            rw [horth k l]
      _ = ∑ k : Fin r, (u k i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [Finset.sum_eq_single k]
            · simp [pow_two]
            · intro l _hl hne
              have hkne : k ≠ l := fun h => hne h.symm
              simp [hkne]
            · intro hnot
              exact (hnot (Finset.mem_univ k)).elim
      _ = P i := by
            dsimp [P]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
  have hsq_le_sum : (P i) ^ 2 ≤ ∑ a : Fin N, (P a) ^ 2 := by
    exact Finset.single_le_sum (fun a _ha => sq_nonneg (P a)) (Finset.mem_univ i)
  have hsq_le : (P i) ^ 2 ≤ P i := by
    simpa [hsum_idem] using hsq_le_sum
  have hPi_le_one : P i ≤ (1 : ℝ) := by
    nlinarith
  simpa [P, pow_two] using hPi_le_one

/-- Bessel's inequality for the finite orthonormal singular-vector families in
the explicit `SVD` structure. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
      (∀ i : Fin n₁, ∑ k : Fin r, (S.u k i) ^ 2 ≤ (1 : ℝ)) ∧
      (∀ j : Fin n₂, ∑ k : Fin r, (S.v k j) ^ 2 ≤ (1 : ℝ)) := by
  exact ⟨coordinate_energy_le_one_of_orthonormal S.u S.u_orthonormal,
    coordinate_energy_le_one_of_orthonormal S.v S.v_orthonormal⟩
